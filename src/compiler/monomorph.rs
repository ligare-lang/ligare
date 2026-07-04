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

    fn rewrite_top(&self, top: TopLevel<'bump>, state: &mut MonoState<'bump>) -> TopLevel<'bump> {
        match top {
            TopLevel::TLEval(t, s) => TopLevel::TLEval(self.rewrite_term(t, state), s),
            TopLevel::TLExpr(t, s) => TopLevel::TLExpr(self.rewrite_term(t, state), s),
            TopLevel::TLDef(n, p, r, b, s) => {
                if p.iter()
                    .any(|(_, c)| c.is_some_and(|t| self.is_erased_param_constraint(t)))
                {
                    return TopLevel::TLDef(n, p, r, b, s);
                }
                let params = self.rewrite_params(p, state);
                let ret = r.map(|t| self.rewrite_type_constraint(t, state));
                let body = self
                    .checker
                    .desugar_with_context(b)
                    .map(|b| self.subst_top_level(b))
                    .unwrap_or(b);
                let body = match ret {
                    Some(ret) => self.rewrite_term_for_constraint(body, ret, state),
                    None => self.rewrite_term(body, state),
                };
                TopLevel::TLDef(n, params, ret, body, s)
            }
            TopLevel::TLExternDef(n, p, r, s) => {
                let params = self.rewrite_params(p, state);
                let ret = self.rewrite_type_constraint(r, state);
                TopLevel::TLExternDef(n, params, ret, s)
            }
            TopLevel::TLInstance(..) => top,
            TopLevel::TLVariable(..) => top,
            TopLevel::TLCheck(t, c, s) => TopLevel::TLCheck(t, c, s),
            TopLevel::TLTheorem(n, p, b, s) => {
                let p = self.rewrite_type_constraint(p, state);
                let b = self.rewrite_term(b, state);
                TopLevel::TLTheorem(n, p, b, s)
            }
            TopLevel::TLUse(..)
            | TopLevel::TLMod(..)
            | TopLevel::TLNamespace(..)
            | TopLevel::TLSplice(..) => top,
            TopLevel::TLPublic(inner) => {
                let rewritten = self.rewrite_top((*inner).clone(), state);
                TopLevel::TLPublic(self.arena.bump().alloc(rewritten))
            }
            TopLevel::TLAttributed(attrs, inner, span) => {
                let rewritten = self.rewrite_top((*inner).clone(), state);
                TopLevel::TLAttributed(attrs, self.arena.bump().alloc(rewritten), span)
            }
        }
    }

    fn rewrite_term(
        &self,
        term: &'bump Term<'bump>,
        state: &mut MonoState<'bump>,
    ) -> &'bump Term<'bump> {
        if let Term::Let(name, val, body, constraint) = term {
            let constraint = constraint.map(|c| self.rewrite_type_constraint(c, state));
            let val = match constraint {
                Some(c) => self.rewrite_term_for_constraint(val, c, state),
                None => self.rewrite_term(val, state),
            };
            let body = self.rewrite_term(body, state);
            return self.arena.let_(name, val, body, constraint);
        }
        if let Term::Annot(inner, constraint) = term {
            return self.arena.annot(
                self.rewrite_term(inner, state),
                self.rewrite_type_constraint(constraint, state),
            );
        }
        if let Term::Lam(body) = term {
            return self.arena.lam(self.rewrite_term(body, state));
        }
        if let Term::NamedLam(name, body) = term {
            return self.arena.named_lam(name, self.rewrite_term(body, state));
        }
        if let Some((base, mono_name, type_args, data_args)) = self.instance_call(term, state) {
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
            if let Some((base, mono_name, type_args, data_args)) = self.instance_call(node, state) {
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
        state: &mut MonoState<'bump>,
    ) -> Option<(
        Name<'bump>,
        Name<'bump>,
        Vec<&'bump Term<'bump>>,
        Vec<&'bump Term<'bump>>,
    )> {
        let term = self.checker.desugar_with_context(term).ok().unwrap_or(term);
        let (head, args) = self.collect_app(term);
        let base = Self::symbol_name(head)?;
        if !state.generic_fns.contains_key(base)
            && let Some(def) = self.generic_fn_from_env(base)
        {
            state.generic_fns.insert(base, def);
        }
        let def = state.generic_fns.get(base)?;
        let max_erased = def.erased_param_indices.iter().copied().max()?;
        if args.len() <= max_erased {
            return None;
        }
        let type_args = def
            .erased_param_indices
            .iter()
            .map(|idx| args[*idx])
            .collect::<Vec<_>>();
        if !type_args.iter().all(|t| self.type_arg_is_supported(t)) {
            return None;
        }
        let data_args = args
            .iter()
            .enumerate()
            .filter_map(|(idx, arg)| (!def.erased_param_indices.contains(&idx)).then_some(*arg))
            .collect::<Vec<_>>();
        Some((base, self.mono_name(base, &type_args), type_args, data_args))
    }

    fn generic_fn_from_env(&self, base: Name<'bump>) -> Option<GenericDef<'bump>> {
        let term = self.env.get(base).copied()?;
        let Term::Annot(body, signature) = *term else {
            return None;
        };
        let mut params = Vec::new();
        let mut erased_param_indices = Vec::new();
        let mut cursor = signature;
        while let Ok(Term::Pi(name, domain, codomain)) = self.checker.evaluator.whnf(cursor) {
            let is_erased = self.is_erased_param_constraint(domain);
            if is_erased {
                erased_param_indices.push(params.len());
            }
            params.push((*name, Some(*domain)));
            cursor = *codomain;
        }
        if erased_param_indices.is_empty() {
            return None;
        }
        Some(GenericDef {
            erased_param_indices,
            params: self.arena.alloc_slice(&params),
            ret: Some(cursor),
            body,
            span: 0..0,
        })
    }

    fn codegen_uses_registered_generics(&self, codegen: &CodegenState<'bump>) -> bool {
        codegen.raw_defs.iter().any(|top| match top {
            TopLevel::TLDef(_, params, ret, body, _) => {
                self.params_use_registered_generics(params)
                    || ret.is_some_and(|ret| self.term_uses_registered_generics(ret))
                    || self.term_uses_registered_generics(body)
            }
            TopLevel::TLExternDef(_, params, ret, _) => {
                self.params_use_registered_generics(params)
                    || self.term_uses_registered_generics(ret)
            }
            _ => false,
        })
    }

    fn params_use_registered_generics(
        &self,
        params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
    ) -> bool {
        params
            .iter()
            .any(|(_, c)| c.is_some_and(|c| self.term_uses_registered_generics(c)))
    }

    fn term_uses_registered_generics(&self, term: &'bump Term<'bump>) -> bool {
        let mut found = false;
        let mut visit = |node| {
            if found {
                return None;
            }
            let (head, args) = self.collect_app(node);
            if let Some(name) = Self::symbol_name(head) {
                found = self.generic_fn_from_env(name).is_some()
                    || self.checker.lookup_enum(name).is_some_and(|(_, params)| {
                        !params.is_empty() && args.len() >= params.len()
                    })
                    || self.checker.lookup_struct(name).is_some_and(|(_, params)| {
                        !params.is_empty() && args.len() >= params.len()
                    });
            }
            None
        };
        self.arena.map_mut(term, &mut visit);
        found
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
        let def = self.generic_type_def(base, generic_types)?;
        let n_params = def.n_params;
        if n_params == 0 || args.len() < n_params {
            return None;
        }
        let type_args = args[..n_params].to_vec();
        if !type_args.iter().all(|t| self.type_arg_is_supported(t)) {
            return None;
        }
        let data_args = args[n_params..].to_vec();
        Some((
            base,
            self.type_mono_name(base, &type_args, &def.layout_param_indices),
            type_args,
            data_args,
        ))
    }

    fn instantiate_generic(
        &self,
        def: &GenericDef<'bump>,
        type_args: &[&'bump Term<'bump>],
        state: &mut MonoState<'bump>,
    ) -> InstantiatedGeneric<'bump> {
        let data_params = def
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, (n, c))| {
                if def.erased_param_indices.contains(&idx) {
                    return None;
                }
                Some((
                    *n,
                    c.map(|t| {
                        let replaced =
                            self.replace_param_vars(t, type_args, &def.erased_param_indices, idx);
                        self.rewrite_type_constraint(replaced, state)
                    }),
                ))
            })
            .collect::<Vec<_>>();
        let body = self.apply_erased_params(def.body, def, type_args);
        let ret = def.ret.map(|t| {
            let replaced =
                self.replace_param_vars(t, type_args, &def.erased_param_indices, def.params.len());
            self.rewrite_type_constraint(replaced, state)
        });
        let body = match ret {
            Some(ret) => self.rewrite_term_for_constraint(body, ret, state),
            None => self.rewrite_term(body, state),
        };
        (self.arena.alloc_slice(&data_params), ret, body)
    }

    fn instantiated_data_param_constraints(
        &self,
        def: &GenericDef<'bump>,
        type_args: &[&'bump Term<'bump>],
    ) -> Vec<Option<&'bump Term<'bump>>> {
        def.params
            .iter()
            .enumerate()
            .filter_map(|(idx, (_, c))| {
                if def.erased_param_indices.contains(&idx) {
                    return None;
                }
                Some(
                    c.map(|t| {
                        self.replace_param_vars(t, type_args, &def.erased_param_indices, idx)
                    }),
                )
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
        if let Term::Lam(body) = term {
            return self
                .arena
                .lam(self.rewrite_term_for_constraint(body, constraint, state));
        }
        if let Term::NamedLam(name, body) = term {
            return self.arena.named_lam(
                name,
                self.rewrite_term_for_constraint(body, constraint, state),
            );
        }
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
        if let Term::Annot(inner, _) = term {
            return self.rewrite_constructed_type(inner, mono_type, type_args, state);
        }
        if let Some((uname, idx, fields, args)) = self.collect_variant_args(term)
            && args.len() == fields.len()
        {
            let params = self
                .checker
                .lookup_enum(uname)
                .map(|(_, params)| params)
                .unwrap_or(&[]);
            let rewritten = self.rewrite_fields(&args, fields, params, type_args, state);
            return self
                .arena
                .variant(mono_type, idx, self.arena.alloc_slice(&rewritten));
        }
        if let Term::Builtin(name) | Term::Global(name) = term
            && let Some((uname, idx, fields)) = self.checker.lookup_variant(name)
            && fields.is_empty()
        {
            let _ = uname;
            return self.arena.variant(mono_type, idx, &[]);
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
        if let Term::Builtin(name) | Term::Global(name) = term
            && let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
            && fields.is_empty()
        {
            let _ = sname;
            return self.arena.struct_cons(mono_type, &[]);
        }
        match term {
            Term::Variant(uname, idx, payloads) => {
                let fields = self
                    .checker
                    .lookup_enum(uname)
                    .and_then(|(def, _)| match def {
                        Term::EnumDef(_, variants) => variants.get(*idx).map(|(_, f)| *f),
                        _ => None,
                    })
                    .unwrap_or(&[]);
                let params = self
                    .checker
                    .lookup_enum(uname)
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
