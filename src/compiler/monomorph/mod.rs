use std::collections::{HashMap, HashSet};

use crate::backend::ir::FunSig;
use crate::core::debruijn::Desugarer;
use crate::core::semantics::SemanticQueries;
use crate::core::syntax::{Name, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::TopLevel;

use super::{CodegenState, Compiler, MonomorphizedProgram};

mod replace;
mod rewrite;

#[derive(Clone)]
struct GenericDef<'bump> {
    erased_param_indices: Vec<usize>,
    params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
    ret: Option<&'bump Term<'bump>>,
    body: &'bump Term<'bump>,
    span: std::ops::Range<usize>,
}

#[derive(Clone)]
struct GenericTypeDef<'bump> {
    n_params: usize,
    layout_param_indices: Vec<usize>,
    body: &'bump Term<'bump>,
}

type Instance<'bump> = (Name<'bump>, Name<'bump>, Vec<&'bump Term<'bump>>);
type InstantiatedGeneric<'bump> = (
    &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
    Option<&'bump Term<'bump>>,
    &'bump Term<'bump>,
);

struct MonoState<'bump> {
    generic_fns: HashMap<Name<'bump>, GenericDef<'bump>>,
    generic_types: HashMap<Name<'bump>, GenericTypeDef<'bump>>,
    seen_fns: HashSet<String>,
    fn_instances: Vec<Instance<'bump>>,
    seen_types: HashSet<String>,
    type_instances: Vec<Instance<'bump>>,
}

impl<'bump> MonoState<'bump> {
    fn new(
        generic_fns: HashMap<Name<'bump>, GenericDef<'bump>>,
        generic_types: HashMap<Name<'bump>, GenericTypeDef<'bump>>,
    ) -> Self {
        Self {
            generic_fns,
            generic_types,
            seen_fns: HashSet::new(),
            fn_instances: Vec::new(),
            seen_types: HashSet::new(),
            type_instances: Vec::new(),
        }
    }

    fn record_fn(&mut self, mono_name: Name<'bump>, instance: Instance<'bump>) {
        if self.seen_fns.insert(mono_name.to_string()) {
            self.fn_instances.push(instance);
        }
    }

    fn record_type(&mut self, mono_name: Name<'bump>, instance: Instance<'bump>) {
        if self.seen_types.insert(mono_name.to_string()) {
            self.type_instances.push(instance);
        }
    }
}

impl<'bump> Compiler<'bump> {
    pub(crate) fn monomorphize_for_codegen(
        &mut self,
        tops: Vec<TopLevel<'bump>>,
        mut codegen: CodegenState<'bump>,
    ) -> Result<MonomorphizedProgram<'bump>, Diagnostic> {
        let generic_fns =
            Self::generic_defs(&codegen.raw_defs, |t| self.is_erased_param_constraint(t));
        let generic_types = self.generic_type_defs(&tops);
        if generic_fns.is_empty()
            && generic_types.is_empty()
            && !self.codegen_uses_registered_generics(&codegen)
        {
            self.rebuild_fun_sigs(&mut codegen)?;
            return Ok(MonomorphizedProgram { tops, codegen });
        }
        let mut state = MonoState::new(generic_fns, generic_types);

        let rewritten: Vec<_> = tops
            .into_iter()
            .map(|top| self.rewrite_top(top, &mut state))
            .collect();

        self.refresh_type_defs(&mut codegen, &mut state);

        codegen.raw_defs = codegen
            .raw_defs
            .into_iter()
            .filter_map(|top| {
                if self.top_has_erased_params(&top) {
                    return None;
                }
                Some(self.rewrite_top(top, &mut state))
            })
            .collect::<Vec<_>>();

        let desugarer = Desugarer::new(self.arena);
        let mut idx = 0;
        while idx < state.fn_instances.len() {
            let (base, mono_name, type_args) = state.fn_instances[idx].clone();
            idx += 1;
            let Some(def) = state.generic_fns.get(base).cloned() else {
                continue;
            };
            let span = def.span.clone();
            let (params, ret, body) = self.instantiate_generic(&def, &type_args, &mut state);
            self.refresh_type_defs(&mut codegen, &mut state);
            let desugared = desugarer.desugar(self.subst_top_level(body));
            codegen
                .raw_defs
                .push(TopLevel::TLDef(mono_name, params, ret, desugared, span));
        }

        self.refresh_type_defs(&mut codegen, &mut state);
        self.rebuild_fun_sigs(&mut codegen)?;
        self.refresh_env_for_codegen(&codegen.raw_defs);
        self.refresh_env_for_codegen(&rewritten);
        Ok(MonomorphizedProgram {
            tops: rewritten,
            codegen,
        })
    }

    fn generic_defs(
        raw_defs: &[TopLevel<'bump>],
        is_erased_param_constraint: impl Fn(&Term<'_>) -> bool,
    ) -> HashMap<Name<'bump>, GenericDef<'bump>> {
        raw_defs
            .iter()
            .filter_map(|top| {
                let TopLevel::TLDef(name, params, ret, body, span) = top else {
                    return None;
                };
                let erased_param_indices = params
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, (_, c))| {
                        c.is_some_and(&is_erased_param_constraint).then_some(idx)
                    })
                    .collect::<Vec<_>>();
                (!erased_param_indices.is_empty()).then_some((
                    *name,
                    GenericDef {
                        erased_param_indices,
                        params,
                        ret: *ret,
                        body,
                        span: span.clone(),
                    },
                ))
            })
            .collect()
    }

    fn generic_type_defs(
        &self,
        tops: &[TopLevel<'bump>],
    ) -> HashMap<Name<'bump>, GenericTypeDef<'bump>> {
        tops.iter()
            .filter_map(|top| {
                let TopLevel::TLDef(name, params, _ret, body, _span) = top else {
                    return None;
                };
                let n_params = params.len();
                if n_params == 0 || !matches!(body, Term::EnumDef(..) | Term::StructDef(..)) {
                    return None;
                }
                let layout_param_indices = params
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, (_, c))| {
                        c.is_some_and(Self::is_type_layout_param_constraint)
                            .then_some(idx)
                    })
                    .chain(Self::layout_param_indices_from_body(body, n_params))
                    .collect::<HashSet<_>>()
                    .into_iter()
                    .collect();
                let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
                let body = self.checker.desugar_with_names_context(body, &names).ok()?;
                Some((
                    *name,
                    GenericTypeDef {
                        n_params,
                        layout_param_indices,
                        body,
                    },
                ))
            })
            .collect()
    }

    fn instantiate_generic_type(
        &self,
        mono_name: Name<'bump>,
        def: &GenericTypeDef<'bump>,
        type_args: &[&'bump Term<'bump>],
        state: &mut MonoState<'bump>,
    ) -> &'bump Term<'bump> {
        match def.body {
            Term::EnumDef(_, variants) => {
                let variants = variants
                    .iter()
                    .map(|(vname, fields)| {
                        let fields = fields
                            .iter()
                            .map(|(fname, c)| {
                                let replaced =
                                    self.replace_type_param_vars(c, type_args, def.n_params);
                                (*fname, self.rewrite_type_constraint(replaced, state))
                            })
                            .collect::<Vec<_>>();
                        (*vname, self.arena.alloc_slice(&fields))
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .enum_def(mono_name, self.arena.alloc_slice(&variants))
            }
            Term::StructDef(_, fields) => {
                let fields = fields
                    .iter()
                    .map(|(fname, c)| {
                        let replaced = self.replace_type_param_vars(c, type_args, def.n_params);
                        (*fname, self.rewrite_type_constraint(replaced, state))
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .struct_def(mono_name, self.arena.alloc_slice(&fields))
            }
            _ => def.body,
        }
    }

    fn refresh_type_defs(&self, codegen: &mut CodegenState<'bump>, state: &mut MonoState<'bump>) {
        let mut enum_types = Vec::new();
        let mut struct_types = Vec::new();
        let instances = state.type_instances.clone();
        for (base, mono_name, type_args) in instances {
            let Some(def) = self.generic_type_def(base, &state.generic_types) else {
                continue;
            };
            let instantiated = self.instantiate_generic_type(mono_name, &def, &type_args, state);
            match instantiated {
                Term::EnumDef(..) => enum_types.push((mono_name, instantiated)),
                Term::StructDef(..) => struct_types.push((mono_name, instantiated)),
                _ => {}
            }
        }
        codegen.enum_types = enum_types;
        codegen.struct_types = struct_types;
    }

    fn generic_type_def(
        &self,
        base: Name<'bump>,
        generic_types: &HashMap<Name<'bump>, GenericTypeDef<'bump>>,
    ) -> Option<GenericTypeDef<'bump>> {
        generic_types.get(base).cloned().or_else(|| {
            self.checker
                .lookup_enum(base)
                .map(|(body, params)| GenericTypeDef {
                    n_params: params.len(),
                    layout_param_indices: Self::layout_param_indices_from_body(body, params.len()),
                    body,
                })
                .or_else(|| {
                    self.checker
                        .lookup_struct(base)
                        .map(|(body, params)| GenericTypeDef {
                            n_params: params.len(),
                            layout_param_indices: Self::layout_param_indices_from_body(
                                body,
                                params.len(),
                            ),
                            body,
                        })
                })
        })
    }

    fn rebuild_fun_sigs(&self, codegen: &mut CodegenState<'bump>) -> Result<(), Diagnostic> {
        let enum_names = codegen
            .enum_types
            .iter()
            .map(|(n, _)| n.to_string())
            .collect::<HashSet<_>>();
        let struct_names = codegen
            .struct_types
            .iter()
            .map(|(n, _)| n.to_string())
            .collect::<HashSet<_>>();
        let mut fun_sigs = Vec::new();
        for top in &codegen.raw_defs {
            if matches!(top, TopLevel::TLDef(name, ..) if name.starts_with(crate::config::GLOBAL_ALLOCATOR_NAME_PREFIX))
            {
                continue;
            }
            if let TopLevel::TLDef(name, params, ret, body, _) = top
                && (!params.is_empty() || matches!(body, Term::Lam(_) | Term::Annot(_, _)))
            {
                let sig = FunSig::from_func(params, *ret, body, &enum_names, &struct_names)?;
                fun_sigs.push((*name, sig));
            } else if let TopLevel::TLExternDef(name, params, ret, _) = top {
                let sig = FunSig::from_extern(params, ret, &enum_names, &struct_names)?;
                fun_sigs.push((*name, sig));
            }
        }
        codegen.fun_sigs = fun_sigs;
        Ok(())
    }

    fn refresh_env_for_codegen(&mut self, tops: &[TopLevel<'bump>]) {
        for top in tops {
            if self.top_has_erased_params(top) {
                continue;
            }
            if let TopLevel::TLDef(name, _params, _ret, body, _) = top {
                if Self::contains_do(body) {
                    continue;
                }
                let actual_name = self.codegen_attribute_target_name(name);
                self.env.insert(actual_name, body);
            }
        }
    }

    fn top_has_erased_params(&self, top: &TopLevel<'bump>) -> bool {
        match top {
            TopLevel::TLDef(_, params, _, _, _) | TopLevel::TLExternDef(_, params, _, _) => params
                .iter()
                .any(|(_, c)| c.is_some_and(|t| self.is_erased_param_constraint(t))),
            TopLevel::TLPublic(inner) | TopLevel::TLAttributed(_, inner, _) => {
                self.top_has_erased_params(inner)
            }
            _ => false,
        }
    }

    fn collect_app(
        &self,
        term: &'bump Term<'bump>,
    ) -> (&'bump Term<'bump>, Vec<&'bump Term<'bump>>) {
        let mut args = Vec::new();
        let mut cur = term;
        while let Term::App(f, a) = cur {
            args.push(*a);
            cur = f;
        }
        args.reverse();
        (cur, args)
    }

    fn is_erased_param_constraint(&self, term: &Term<'_>) -> bool {
        SemanticQueries::new(self.checker.builtins()).is_erased_parameter_constraint(term)
    }

    fn type_arg_is_supported(&self, term: &Term<'_>) -> bool {
        matches!(
            term,
            Term::Builtin(_)
                | Term::Global(_)
                | Term::App(_, _)
                | Term::StructCons(..)
                | Term::Variant(..)
                | Term::Annot(_, _)
                | Term::LitInt(_)
        )
    }

    fn is_type_layout_param_constraint(term: &Term<'_>) -> bool {
        matches!(term, Term::Builtin("prop") | Term::Global("prop"))
    }

    fn layout_param_indices_from_body(body: &Term<'_>, n_params: usize) -> Vec<usize> {
        let mut indices = HashSet::new();
        match body {
            Term::EnumDef(_, variants) => {
                for (_, fields) in variants.iter() {
                    for (_, constraint) in fields.iter() {
                        Self::collect_direct_layout_param(constraint, n_params, &mut indices);
                    }
                }
            }
            Term::StructDef(_, fields) => {
                for (_, constraint) in fields.iter() {
                    Self::collect_direct_layout_param(constraint, n_params, &mut indices);
                }
            }
            _ => {}
        }
        let mut indices = indices.into_iter().collect::<Vec<_>>();
        indices.sort_unstable();
        indices
    }

    fn collect_direct_layout_param(term: &Term<'_>, n_params: usize, indices: &mut HashSet<usize>) {
        match term {
            Term::Var(i) if *i < n_params => {
                indices.insert(n_params - 1 - i);
            }
            Term::Annot(inner, _) | Term::Unsafe(inner) | Term::Pure(inner) => {
                Self::collect_direct_layout_param(inner, n_params, indices);
            }
            Term::Refine(_, parent, _) => {
                Self::collect_direct_layout_param(parent, n_params, indices);
            }
            _ => {}
        }
    }

    fn mono_name(&self, base: Name<'bump>, type_args: &[&Term<'_>]) -> Name<'bump> {
        let suffix = type_args
            .iter()
            .map(|t| self.type_arg_slug(t))
            .collect::<Vec<_>>()
            .join("__");
        let base = base.replace(|c: char| !c.is_ascii_alphanumeric(), "_");
        self.arena.alloc_str(&format!("{base}__{suffix}"))
    }

    fn type_mono_name(
        &self,
        base: Name<'bump>,
        type_args: &[&Term<'_>],
        layout_param_indices: &[usize],
    ) -> Name<'bump> {
        let layout_args = layout_param_indices
            .iter()
            .filter_map(|idx| type_args.get(*idx).copied())
            .collect::<Vec<_>>();
        if layout_args.is_empty() {
            let base = base.replace(|c: char| !c.is_ascii_alphanumeric(), "_");
            self.arena.alloc_str(&base)
        } else {
            self.mono_name(base, &layout_args)
        }
    }

    fn type_arg_slug(&self, term: &Term<'_>) -> String {
        if let Some(n) = self.peano_nat_value(term) {
            return format!("n{n}");
        }
        match term {
            Term::LitInt(n) => format!("i{n}").replace('-', "neg"),
            Term::Builtin(n) | Term::Global(n) => {
                n.replace(|c: char| !c.is_ascii_alphanumeric(), "_")
            }
            Term::App(f, a) => format!("{}__{}", self.type_arg_slug(f), self.type_arg_slug(a)),
            Term::StructCons(name, values) => format!(
                "{}__{}",
                name.replace(|c: char| !c.is_ascii_alphanumeric(), "_"),
                values
                    .iter()
                    .map(|v| self.type_arg_slug(v))
                    .collect::<Vec<_>>()
                    .join("__")
            ),
            Term::Variant(name, idx, _) => format!(
                "{}__v{}",
                name.replace(|c: char| !c.is_ascii_alphanumeric(), "_"),
                idx
            ),
            Term::Annot(inner, _) => self.type_arg_slug(inner),
            _ => "unknown".to_string(),
        }
    }

    fn peano_nat_value(&self, term: &Term<'_>) -> Option<u64> {
        match term {
            Term::Builtin(name) | Term::Global(name) if is_zero_name(name) => Some(0),
            Term::App(head, pred) if matches!(**head, Term::Builtin(name) | Term::Global(name) if is_succ_name(name)) => {
                self.peano_nat_value(pred).map(|n| n + 1)
            }
            Term::Variant(name, 0, payloads) if payloads.is_empty() && is_nat_name(name) => Some(0),
            Term::Variant(name, 1, payloads) if payloads.len() == 1 && is_nat_name(name) => {
                self.peano_nat_value(payloads[0]).map(|n| n + 1)
            }
            Term::Annot(inner, _) => self.peano_nat_value(inner),
            _ => None,
        }
    }

    fn apply_erased_params(
        &self,
        term: &'bump Term<'bump>,
        def: &GenericDef<'bump>,
        args: &[&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        self.apply_erased_params_at(term, def, args, 0)
    }

    fn apply_erased_params_at(
        &self,
        term: &'bump Term<'bump>,
        def: &GenericDef<'bump>,
        args: &[&'bump Term<'bump>],
        param_idx: usize,
    ) -> &'bump Term<'bump> {
        if param_idx >= def.params.len() {
            return term;
        }
        let sub = crate::core::debruijn::SubstitutionContext::new(self.arena);
        let body = match term {
            Term::Annot(inner, _) => inner,
            _ => term,
        };
        let Term::Lam(lam_body) = body else {
            return body;
        };
        if let Some(arg_idx) = def
            .erased_param_indices
            .iter()
            .position(|idx| *idx == param_idx)
        {
            let body = sub.beta(lam_body, args[arg_idx]);
            self.apply_erased_params_at(body, def, args, param_idx + 1)
        } else {
            self.arena
                .lam(self.apply_erased_params_at(lam_body, def, args, param_idx + 1))
        }
    }
}

fn is_nat_name(name: &str) -> bool {
    name == "Nat" || name.ends_with("::Nat")
}

fn is_zero_name(name: &str) -> bool {
    name == "Zero" || name.ends_with("::Zero")
}

fn is_succ_name(name: &str) -> bool {
    name == "Succ" || name.ends_with("::Succ")
}
