use std::collections::{HashMap, HashSet};

use crate::backend::ir::FunSig;
use crate::core::debruijn::Desugarer;
use crate::core::semantics::SemanticQueries;
use crate::core::syntax::{Name, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::TopLevel;

use super::{CodegenState, Compiler, MonomorphizedProgram};

mod replace;

#[derive(Clone)]
struct GenericDef<'bump> {
    n_type_params: usize,
    params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
    ret: Option<&'bump Term<'bump>>,
    body: &'bump Term<'bump>,
    span: std::ops::Range<usize>,
}

#[derive(Clone)]
struct GenericTypeDef<'bump> {
    n_type_params: usize,
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
        if generic_fns.is_empty() && generic_types.is_empty() {
            self.rebuild_fun_sigs(&mut codegen)?;
            return Ok(MonomorphizedProgram { tops, codegen });
        }

        let mut state = MonoState::new(generic_fns, generic_types);

        let rewritten: Vec<_> = tops
            .into_iter()
            .map(|top| self.rewrite_top(top, &mut state))
            .collect();

        self.refresh_type_defs(&mut codegen, &state.generic_types, &state.type_instances);

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
            self.refresh_type_defs(&mut codegen, &state.generic_types, &state.type_instances);
            let desugared = desugarer.desugar(self.subst_top_level(body));
            codegen
                .raw_defs
                .push(TopLevel::TLDef(mono_name, params, ret, desugared, span));
        }

        self.refresh_type_defs(&mut codegen, &state.generic_types, &state.type_instances);
        self.rebuild_fun_sigs(&mut codegen)?;
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
                let n_type_params = params
                    .iter()
                    .take_while(|(_, c)| c.is_some_and(&is_erased_param_constraint))
                    .count();
                (n_type_params > 0).then_some((
                    *name,
                    GenericDef {
                        n_type_params,
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
                let n_type_params = params
                    .iter()
                    .take_while(|(_, c)| c.is_some_and(|t| self.is_erased_param_constraint(t)))
                    .count();
                if n_type_params == 0 || !matches!(body, Term::UnionDef(..) | Term::StructDef(..)) {
                    return None;
                }
                let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
                let body = self.checker.desugar_with_names_context(body, &names).ok()?;
                Some((
                    *name,
                    GenericTypeDef {
                        n_type_params,
                        body,
                    },
                ))
            })
            .collect()
    }

    fn rewrite_top(&self, top: TopLevel<'bump>, state: &mut MonoState<'bump>) -> TopLevel<'bump> {
        match top {
            TopLevel::TLShow(t, s) => TopLevel::TLShow(self.rewrite_term(t, state), s),
            TopLevel::TLExpr(t, s) => TopLevel::TLExpr(self.rewrite_term(t, state), s),
            TopLevel::TLDef(n, p, r, b, s) => {
                if p.iter()
                    .any(|(_, c)| c.is_some_and(|t| self.is_erased_param_constraint(t)))
                {
                    return TopLevel::TLDef(n, p, r, b, s);
                }
                let params = self.rewrite_params(p, state);
                let ret = r.map(|t| self.rewrite_type_constraint(t, state));
                let body = self.rewrite_term(b, state);
                TopLevel::TLDef(n, params, ret, body, s)
            }
            TopLevel::TLCheck(t, c, s) => TopLevel::TLCheck(t, c, s),
            TopLevel::TLTheorem(n, p, b, s) => {
                let p = self.rewrite_type_constraint(p, state);
                let b = self.rewrite_term(b, state);
                TopLevel::TLTheorem(n, p, b, s)
            }
            TopLevel::TLUse(..) => top,
            TopLevel::TLPublic(inner) => {
                let rewritten = self.rewrite_top((*inner).clone(), state);
                TopLevel::TLPublic(self.arena.bump().alloc(rewritten))
            }
        }
    }

    fn rewrite_term(
        &self,
        term: &'bump Term<'bump>,
        state: &mut MonoState<'bump>,
    ) -> &'bump Term<'bump> {
        if let Some((base, mono_name, type_args, data_args)) =
            self.instance_call(term, &state.generic_fns)
        {
            state.record_fn(mono_name, (base, mono_name, type_args.clone()));
            let expected = self.instantiated_data_param_constraints(
                state
                    .generic_fns
                    .get(base)
                    .expect("generic function must exist"),
                &type_args,
            );
            return data_args.iter().enumerate().fold(
                self.arena.builtin(mono_name),
                |f, (idx, a)| {
                    let arg = match expected.get(idx).copied().flatten() {
                        Some(c) => self.rewrite_term_for_constraint(a, c, state),
                        None => self.rewrite_term(a, state),
                    };
                    self.arena.app(f, arg)
                },
            );
        }
        let mut rewrite = |node| {
            if let Some((base, mono_name, type_args, data_args)) =
                self.instance_call(node, &state.generic_fns)
            {
                state.record_fn(mono_name, (base, mono_name, type_args.clone()));
                let expected = self.instantiated_data_param_constraints(
                    state
                        .generic_fns
                        .get(base)
                        .expect("generic function must exist"),
                    &type_args,
                );
                return Some(data_args.iter().enumerate().fold(
                    self.arena.builtin(mono_name),
                    |f, (idx, a)| {
                        let arg = match expected.get(idx).copied().flatten() {
                            Some(c) => self.rewrite_term_for_constraint(a, c, state),
                            None => self.rewrite_term(a, state),
                        };
                        self.arena.app(f, arg)
                    },
                ));
            }
            self.type_instance(node, &state.generic_types).map(
                |(base, mono_name, type_args, data_args)| {
                    let _ = data_args;
                    state.record_type(mono_name, (base, mono_name, type_args));
                    self.arena.builtin(mono_name)
                },
            )
        };
        self.arena.map_mut(term, &mut rewrite)
    }

    fn instance_call(
        &self,
        term: &'bump Term<'bump>,
        generics: &HashMap<Name<'bump>, GenericDef<'bump>>,
    ) -> Option<(
        Name<'bump>,
        Name<'bump>,
        Vec<&'bump Term<'bump>>,
        Vec<&'bump Term<'bump>>,
    )> {
        let term = self.checker.desugar_with_context(term).ok().unwrap_or(term);
        let (head, args) = self.collect_app(term);
        let base = Self::symbol_name(head)?;
        let def = generics.get(base)?;
        let n_type_params = def.n_type_params;
        if n_type_params == 0 || args.len() < n_type_params {
            return None;
        }
        let type_args = args[..n_type_params].to_vec();
        if !type_args.iter().all(|t| self.type_arg_is_supported(t)) {
            return None;
        }
        let data_args = args[n_type_params..].to_vec();
        Some((base, self.mono_name(base, &type_args), type_args, data_args))
    }

    fn type_instance(
        &self,
        term: &'bump Term<'bump>,
        generic_types: &HashMap<Name<'bump>, GenericTypeDef<'bump>>,
    ) -> Option<(
        Name<'bump>,
        Name<'bump>,
        Vec<&'bump Term<'bump>>,
        Vec<&'bump Term<'bump>>,
    )> {
        let term = self.checker.desugar_with_context(term).ok().unwrap_or(term);
        let (head, args) = self.collect_app(term);
        let base = Self::symbol_name(head)?;
        let def = generic_types.get(base)?;
        let n_type_params = def.n_type_params;
        if n_type_params == 0 || args.len() < n_type_params {
            return None;
        }
        let type_args = args[..n_type_params].to_vec();
        if !type_args.iter().all(|t| self.type_arg_is_supported(t)) {
            return None;
        }
        let data_args = args[n_type_params..].to_vec();
        Some((base, self.mono_name(base, &type_args), type_args, data_args))
    }

    fn instantiate_generic(
        &self,
        def: &GenericDef<'bump>,
        type_args: &[&'bump Term<'bump>],
        state: &mut MonoState<'bump>,
    ) -> InstantiatedGeneric<'bump> {
        let n_type_params = def.n_type_params;

        let data_params = def.params[n_type_params..]
            .iter()
            .enumerate()
            .map(|(idx, (n, c))| {
                (
                    *n,
                    c.map(|t| {
                        let replaced =
                            self.replace_type_param_vars(t, type_args, n_type_params + idx);
                        self.rewrite_type_constraint(replaced, state)
                    }),
                )
            })
            .collect::<Vec<_>>();
        let body = self.replace_type_param_vars(
            self.peel_lams(def.body, n_type_params),
            type_args,
            def.params.len(),
        );
        let body = self.rewrite_term(body, state);
        (
            self.arena.alloc_slice(&data_params),
            def.ret.map(|t| {
                let replaced = self.replace_type_param_vars(t, type_args, def.params.len());
                self.rewrite_type_constraint(replaced, state)
            }),
            body,
        )
    }

    fn instantiated_data_param_constraints(
        &self,
        def: &GenericDef<'bump>,
        type_args: &[&'bump Term<'bump>],
    ) -> Vec<Option<&'bump Term<'bump>>> {
        let n_type_params = def.n_type_params;
        def.params[n_type_params..]
            .iter()
            .enumerate()
            .map(|(idx, (_, c))| {
                c.map(|t| self.replace_type_param_vars(t, type_args, n_type_params + idx))
            })
            .collect()
    }

    fn rewrite_params(
        &self,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        state: &mut MonoState<'bump>,
    ) -> &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)] {
        let rewritten = params
            .iter()
            .map(|(n, c)| (*n, c.map(|t| self.rewrite_type_constraint(t, state))))
            .collect::<Vec<_>>();
        self.arena.alloc_slice(&rewritten)
    }

    fn rewrite_type_constraint(
        &self,
        term: &'bump Term<'bump>,
        state: &mut MonoState<'bump>,
    ) -> &'bump Term<'bump> {
        if let Some((base, mono_name, type_args, _)) =
            self.type_instance(term, &state.generic_types)
        {
            state.record_type(mono_name, (base, mono_name, type_args));
            return self.arena.builtin(mono_name);
        }
        let mut rewrite = |node| {
            self.type_instance(node, &state.generic_types)
                .map(|(base, mono_name, type_args, _)| {
                    state.record_type(mono_name, (base, mono_name, type_args));
                    self.arena.builtin(mono_name)
                })
        };
        self.arena.map_mut(term, &mut rewrite)
    }

    fn rewrite_term_for_constraint(
        &self,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
        state: &mut MonoState<'bump>,
    ) -> &'bump Term<'bump> {
        if let Some((base, mono_name, type_args, _)) =
            self.type_instance(constraint, &state.generic_types)
        {
            state.record_type(mono_name, (base, mono_name, type_args.clone()));
            self.rewrite_constructed_type(term, mono_name, &type_args, state)
        } else if let Some((base, mono_name, type_args)) =
            state
                .type_instances
                .iter()
                .find_map(|(base, mono_name, type_args)| {
                    if matches!(constraint, Term::Builtin(n) | Term::Global(n) if *n == *mono_name)
                    {
                        Some((*base, *mono_name, type_args.clone()))
                    } else {
                        None
                    }
                })
        {
            let _ = base;
            self.rewrite_constructed_type(term, mono_name, &type_args, state)
        } else {
            self.rewrite_term(term, state)
        }
    }

    fn rewrite_constructed_type(
        &self,
        term: &'bump Term<'bump>,
        mono_type: Name<'bump>,
        type_args: &[&'bump Term<'bump>],
        state: &mut MonoState<'bump>,
    ) -> &'bump Term<'bump> {
        let term = self.checker.desugar_with_context(term).unwrap_or(term);
        if let Some((uname, idx, fields, args)) = self.collect_variant_args(term)
            && args.len() == fields.len()
        {
            let params = self
                .checker
                .lookup_union(uname)
                .map(|(_, params)| params)
                .unwrap_or(&[]);
            let rewritten = self.rewrite_fields(&args, fields, params, type_args, state);
            return self
                .arena
                .variant(mono_type, idx, self.arena.alloc_slice(&rewritten));
        }
        if let Some((sname, fields, values)) = self.collect_struct_args(term)
            && values.len() == fields.len()
        {
            let params = self
                .checker
                .lookup_struct(sname)
                .map(|(_, params)| params)
                .unwrap_or(&[]);
            let rewritten = self.rewrite_fields(&values, fields, params, type_args, state);
            return self
                .arena
                .struct_cons(mono_type, self.arena.alloc_slice(&rewritten));
        }
        match term {
            Term::Variant(uname, idx, payloads) => {
                let fields = self
                    .checker
                    .lookup_union(uname)
                    .and_then(|(def, _)| match def {
                        Term::UnionDef(_, variants) => variants.get(*idx).map(|(_, f)| *f),
                        _ => None,
                    })
                    .unwrap_or(&[]);
                let params = self
                    .checker
                    .lookup_union(uname)
                    .map(|(_, params)| params)
                    .unwrap_or(&[]);
                let rewritten = self.rewrite_fields(payloads, fields, params, type_args, state);
                self.arena
                    .variant(mono_type, *idx, self.arena.alloc_slice(&rewritten))
            }
            Term::StructCons(sname, values) => {
                let fields = self
                    .checker
                    .lookup_struct(sname)
                    .and_then(|(def, _)| match def {
                        Term::StructDef(_, fields) => Some(*fields),
                        _ => None,
                    })
                    .unwrap_or(&[]);
                let params = self
                    .checker
                    .lookup_struct(sname)
                    .map(|(_, params)| params)
                    .unwrap_or(&[]);
                let rewritten = self.rewrite_fields(values, fields, params, type_args, state);
                self.arena
                    .struct_cons(mono_type, self.arena.alloc_slice(&rewritten))
            }
            Term::Match(scrut, branches) => {
                let scrut = self.rewrite_constructed_type(scrut, mono_type, type_args, state);
                let rewritten = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let binds = binds
                            .iter()
                            .map(|(n, c)| (*n, self.rewrite_type_constraint(c, state)))
                            .collect::<Vec<_>>();
                        (
                            *idx,
                            self.arena.alloc_slice(&binds),
                            self.rewrite_term(body, state),
                        )
                    })
                    .collect::<Vec<_>>();
                self.arena.match_(scrut, self.arena.alloc_slice(&rewritten))
            }
            _ => self.rewrite_term(term, state),
        }
    }

    fn rewrite_fields(
        &self,
        values: &[&'bump Term<'bump>],
        fields: &'bump [(Name<'bump>, &'bump Term<'bump>)],
        _type_params: &'bump [Name<'bump>],
        type_args: &[&'bump Term<'bump>],
        state: &mut MonoState<'bump>,
    ) -> Vec<&'bump Term<'bump>> {
        values
            .iter()
            .enumerate()
            .map(|(i, value)| {
                let expected = fields
                    .get(i)
                    .map(|(_, c)| self.replace_type_param_vars(c, type_args, type_args.len()));
                match expected {
                    Some(c) => self.rewrite_term_for_constraint(value, c, state),
                    None => self.rewrite_term(value, state),
                }
            })
            .collect()
    }

    fn symbol_name(term: &'bump Term<'bump>) -> Option<Name<'bump>> {
        match term {
            Term::Builtin(name) | Term::Global(name) => Some(*name),
            _ => None,
        }
    }

    fn instantiate_generic_type(
        &self,
        mono_name: Name<'bump>,
        def: &GenericTypeDef<'bump>,
        type_args: &[&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        match def.body {
            Term::UnionDef(_, variants) => {
                let variants = variants
                    .iter()
                    .map(|(vname, fields)| {
                        let fields = fields
                            .iter()
                            .map(|(fname, c)| {
                                (
                                    *fname,
                                    self.replace_type_param_vars(c, type_args, def.n_type_params),
                                )
                            })
                            .collect::<Vec<_>>();
                        (*vname, self.arena.alloc_slice(&fields))
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .union_def(mono_name, self.arena.alloc_slice(&variants))
            }
            Term::StructDef(_, fields) => {
                let fields = fields
                    .iter()
                    .map(|(fname, c)| {
                        (
                            *fname,
                            self.replace_type_param_vars(c, type_args, def.n_type_params),
                        )
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .struct_def(mono_name, self.arena.alloc_slice(&fields))
            }
            _ => def.body,
        }
    }

    fn refresh_type_defs(
        &self,
        codegen: &mut CodegenState<'bump>,
        generic_types: &HashMap<Name<'bump>, GenericTypeDef<'bump>>,
        instances: &[(Name<'bump>, Name<'bump>, Vec<&'bump Term<'bump>>)],
    ) {
        let mut union_types = Vec::new();
        let mut struct_types = Vec::new();
        for (base, mono_name, type_args) in instances {
            let Some(def) = generic_types.get(base) else {
                continue;
            };
            let instantiated = self.instantiate_generic_type(mono_name, def, type_args);
            match instantiated {
                Term::UnionDef(..) => union_types.push((*mono_name, instantiated)),
                Term::StructDef(..) => struct_types.push((*mono_name, instantiated)),
                _ => {}
            }
        }
        codegen.union_types = union_types;
        codegen.struct_types = struct_types;
    }

    fn rebuild_fun_sigs(&self, codegen: &mut CodegenState<'bump>) -> Result<(), Diagnostic> {
        let union_names = codegen
            .union_types
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
            if let TopLevel::TLDef(name, params, ret, body, _) = top
                && (!params.is_empty() || matches!(body, Term::Lam(_) | Term::Annot(_, _)))
            {
                let sig = FunSig::from_func(params, *ret, body, &union_names, &struct_names)?;
                fun_sigs.push((*name, sig));
            }
        }
        codegen.fun_sigs = fun_sigs;
        Ok(())
    }

    fn refresh_env_for_codegen(&mut self, tops: &[TopLevel<'bump>]) {
        for top in tops {
            if let TopLevel::TLDef(name, _params, _ret, body, _) = top {
                self.env.insert(*name, body);
            }
        }
    }

    fn top_has_erased_params(&self, top: &TopLevel<'bump>) -> bool {
        matches!(
            top,
            TopLevel::TLDef(_, params, _, _, _)
                if params
                    .iter()
                    .any(|(_, c)| c.is_some_and(|t| self.is_erased_param_constraint(t)))
        )
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

    fn peel_lams(&self, term: &'bump Term<'bump>, count: usize) -> &'bump Term<'bump> {
        let mut t = term;
        let mut remaining = count;
        while remaining > 0 {
            match t {
                Term::Annot(inner, _) => t = inner,
                Term::Lam(body) => {
                    t = body;
                    remaining -= 1;
                }
                _ => break,
            }
        }
        t
    }

    fn is_erased_param_constraint(&self, term: &Term<'_>) -> bool {
        SemanticQueries::new(self.checker.builtins()).is_erased_parameter_constraint(term)
    }

    fn type_arg_is_supported(&self, term: &Term<'_>) -> bool {
        matches!(term, Term::Builtin(_) | Term::Global(_) | Term::App(_, _))
    }

    fn mono_name(&self, base: Name<'bump>, type_args: &[&Term<'_>]) -> Name<'bump> {
        let suffix = type_args
            .iter()
            .map(|t| self.type_arg_slug(t))
            .collect::<Vec<_>>()
            .join("__");
        self.arena.alloc_str(&format!("{base}__{suffix}"))
    }

    fn type_arg_slug(&self, term: &Term<'_>) -> String {
        match term {
            Term::Builtin(n) | Term::Global(n) => {
                n.replace(|c: char| !c.is_ascii_alphanumeric(), "_")
            }
            Term::App(f, a) => format!("{}__{}", self.type_arg_slug(f), self.type_arg_slug(a)),
            _ => "unknown".to_string(),
        }
    }
}
