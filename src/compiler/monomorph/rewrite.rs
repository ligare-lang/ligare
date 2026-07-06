use super::*;

impl<'bump> Compiler<'bump> {
    pub(super) fn rewrite_top(
        &self,
        top: TopLevel<'bump>,
        state: &mut MonoState<'bump>,
    ) -> TopLevel<'bump> {
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
                    .desugar_checked_def(p, r, b)
                    .map(|body| self.subst_top_level(body))
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

    pub(super) fn codegen_uses_registered_generics(
        &self,
        codegen: &CodegenState<'bump>,
    ) -> bool {
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

    pub(super) fn instantiate_generic(
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

    pub(super) fn rewrite_type_constraint(
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
}
