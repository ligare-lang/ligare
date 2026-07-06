use super::*;

mod evaluation;
mod utilities;

impl<'bump> Compiler<'bump> {
    /// Process a single top-level item.
    pub(super) fn process_top_level(&mut self, top: TopLevel<'bump>) -> Result<(), Diagnostic> {
        for top in self.expand_meta_tops(top)? {
            self.process_expanded_top_level(top)?;
        }
        Ok(())
    }

    pub(super) fn process_expanded_top_level(
        &mut self,
        top: TopLevel<'bump>,
    ) -> Result<(), Diagnostic> {
        match top {
            TopLevel::TLDef(name, params, m_ret, body, span) => {
                let params = self.with_scoped_implicit_params(params);
                self.process_def(name, params, m_ret, body, span, TerminationClaim::None)?;
            }
            TopLevel::TLExternDef(name, params, ret, span) => {
                self.process_extern_def(name, params, ret, span)?;
            }
            TopLevel::TLInstance(name, constraint, value, span) => {
                self.process_instance(name, constraint, value, span)?;
            }
            TopLevel::TLVariable(params, _) => {
                self.scoped_implicit_params.extend(params.iter().copied());
            }
            TopLevel::TLCheck(term, constraint, span) => {
                self.process_check(term, constraint, span)?;
            }
            TopLevel::TLTheorem(name, prop, body, span) => {
                self.process_theorem(name, prop, body, span)?;
            }
            TopLevel::TLPublic(inner) => {
                self.process_expanded_top_level((*inner).clone())?;
            }
            TopLevel::TLAttributed(attrs, inner, span) => {
                if attrs.iter().any(|attr| {
                    attr.is_name(COMPILER_INTRINSIC_ATTR)
                        || attr.is_name(COMPILER_BUILTIN_ATTRIBUTE_ATTR)
                }) {
                    return Ok(());
                }
                let claim = self.termination_claim_from_attrs(attrs, span)?;
                if claim.is_user_claim()
                    && self.process_terminating_attributed_top((*inner).clone(), claim)?
                {
                    return Ok(());
                }
                if self.process_meta_callable_attributed_top(attrs, (*inner).clone())? {
                    return Ok(());
                }
                self.process_expanded_top_level((*inner).clone())?;
            }
            TopLevel::TLUse(..) => {}
            TopLevel::TLMod(..) => {}
            TopLevel::TLNamespace(name, items, _) => {
                let scope_len = self.scoped_implicit_params.len();
                for item in items {
                    self.process_namespace_top(name, item.clone())?;
                }
                self.scoped_implicit_params.truncate(scope_len);
            }
            TopLevel::TLEval(term, span) => {
                self.process_eval_like(term, span, "eval")?;
            }
            TopLevel::TLExpr(term, span) => {
                self.process_eval_like(term, span, "eval")?;
            }
            TopLevel::TLSplice(..) => unreachable!("top-level splice should be expanded first"),
        }
        Ok(())
    }

    fn process_namespace_top(
        &mut self,
        namespace: Name<'bump>,
        top: TopLevel<'bump>,
    ) -> Result<(), Diagnostic> {
        self.process_namespace_top_with_termination(namespace, top, TerminationClaim::None)
    }

    fn process_terminating_attributed_top(
        &mut self,
        top: TopLevel<'bump>,
        claim: TerminationClaim<'bump>,
    ) -> Result<bool, Diagnostic> {
        match top {
            TopLevel::TLPublic(inner) => {
                self.process_terminating_attributed_top((*inner).clone(), claim)
            }
            TopLevel::TLDef(name, params, m_ret, body, span) => {
                let params = self.with_scoped_implicit_params(params);
                self.process_def(name, params, m_ret, body, span, claim)?;
                Ok(true)
            }
            TopLevel::TLNamespace(namespace, items, _) => {
                let scope_len = self.scoped_implicit_params.len();
                for item in items {
                    self.process_namespace_top_with_termination(namespace, item.clone(), claim)?;
                }
                self.scoped_implicit_params.truncate(scope_len);
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn process_namespace_top_with_termination(
        &mut self,
        namespace: Name<'bump>,
        top: TopLevel<'bump>,
        termination_claim: TerminationClaim<'bump>,
    ) -> Result<(), Diagnostic> {
        let qualify = |name: Name<'bump>| self.arena.alloc_str(&format!("{namespace}::{name}"));
        match top {
            TopLevel::TLPublic(inner) => self.process_namespace_top_with_termination(
                namespace,
                (*inner).clone(),
                termination_claim,
            ),
            TopLevel::TLAttributed(attrs, inner, span) => {
                if attrs.iter().any(|attr| {
                    attr.is_name(COMPILER_INTRINSIC_ATTR)
                        || attr.is_name(COMPILER_BUILTIN_ATTRIBUTE_ATTR)
                }) {
                    return Ok(());
                }
                let termination_claim =
                    termination_claim.merge(self.termination_claim_from_attrs(attrs, span)?);
                if self.process_namespace_meta_callable_attributed_top(
                    namespace,
                    attrs,
                    (*inner).clone(),
                    termination_claim,
                )? {
                    return Ok(());
                }
                self.process_namespace_top_with_termination(
                    namespace,
                    (*inner).clone(),
                    termination_claim,
                )
            }
            TopLevel::TLDef(name, params, ret, body, span) => {
                let params = self.with_scoped_implicit_params(params);
                self.process_def(qualify(name), params, ret, body, span, termination_claim)
            }
            TopLevel::TLExternDef(name, params, ret, span) => {
                self.process_extern_def(qualify(name), params, ret, span)
            }
            TopLevel::TLInstance(name, constraint, value, span) => {
                self.process_instance(qualify(name), constraint, value, span)
            }
            TopLevel::TLVariable(params, _) => {
                self.scoped_implicit_params.extend(params.iter().copied());
                Ok(())
            }
            TopLevel::TLTheorem(name, prop, body, span) => {
                self.process_theorem(qualify(name), prop, body, span)
            }
            _ => Ok(()),
        }
    }

    fn with_scoped_implicit_params(
        &self,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
    ) -> &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)] {
        if self.scoped_implicit_params.is_empty() {
            return params;
        }
        let mut all = Vec::with_capacity(self.scoped_implicit_params.len() + params.len());
        all.extend(self.scoped_implicit_params.iter().copied());
        all.extend(params.iter().copied());
        self.arena.alloc_slice(&all)
    }

    fn process_meta_callable_attributed_top(
        &mut self,
        attrs: &'bump [crate::front::parser::Attribute<'bump>],
        top: TopLevel<'bump>,
    ) -> Result<bool, Diagnostic> {
        let has_tactic = attrs.iter().any(|attr| attr.is_name(TACTIC_ATTR));
        let has_attr = attrs.iter().any(|attr| attr.is_name(CUSTOM_ATTRIBUTE_ATTR));
        if !has_tactic && !has_attr {
            return Ok(false);
        }
        match top {
            TopLevel::TLPublic(inner) => {
                self.process_meta_callable_attributed_top(attrs, (*inner).clone())
            }
            TopLevel::TLDef(name, params, m_ret, body, span) => {
                let params = self.with_scoped_implicit_params(params);
                self.validate_and_register_meta_markers(
                    name,
                    params,
                    m_ret,
                    has_tactic,
                    has_attr,
                    span.clone(),
                )?;
                self.process_def(name, params, m_ret, body, span, TerminationClaim::None)?;
                Ok(true)
            }
            _ => Err(Diagnostic::new(
                "#[tactic] and #[attr] may only prefix `def`",
            )),
        }
    }

    fn process_namespace_meta_callable_attributed_top(
        &mut self,
        namespace: Name<'bump>,
        attrs: &'bump [crate::front::parser::Attribute<'bump>],
        top: TopLevel<'bump>,
        termination_claim: TerminationClaim<'bump>,
    ) -> Result<bool, Diagnostic> {
        let has_tactic = attrs.iter().any(|attr| attr.is_name(TACTIC_ATTR));
        let has_attr = attrs.iter().any(|attr| attr.is_name(CUSTOM_ATTRIBUTE_ATTR));
        if !has_tactic && !has_attr {
            return Ok(false);
        }
        let qualify = |name: Name<'bump>| self.arena.alloc_str(&format!("{namespace}::{name}"));
        match top {
            TopLevel::TLPublic(inner) => self.process_namespace_meta_callable_attributed_top(
                namespace,
                attrs,
                (*inner).clone(),
                termination_claim,
            ),
            TopLevel::TLDef(name, params, m_ret, body, span) => {
                let qname = qualify(name);
                let params = self.with_scoped_implicit_params(params);
                self.validate_and_register_meta_markers(
                    qname,
                    params,
                    m_ret,
                    has_tactic,
                    has_attr,
                    span.clone(),
                )?;
                self.process_def(qname, params, m_ret, body, span, termination_claim)?;
                Ok(true)
            }
            _ => Err(Diagnostic::new(
                "#[tactic] and #[attr] may only prefix `def`",
            )),
        }
    }

    fn validate_and_register_meta_markers(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        ret: Option<&'bump Term<'bump>>,
        has_tactic: bool,
        has_attr: bool,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        if has_tactic {
            self.validate_meta_callable_signature(
                name,
                params,
                ret,
                MetaSignatureSpec {
                    marker: TACTIC_ATTR,
                    first: crate::compiler::meta::EXPR_TYPE,
                    output: crate::compiler::meta::EXPR_TYPE,
                    span: span.clone(),
                },
            )?;
            self.tactics.insert(
                name,
                MetaCallable {
                    name,
                    params: params.iter().map(|(_, c)| *c).collect(),
                },
            );
        }
        if has_attr {
            self.validate_meta_callable_signature(
                name,
                params,
                ret,
                MetaSignatureSpec {
                    marker: CUSTOM_ATTRIBUTE_ATTR,
                    first: crate::compiler::meta::EXPR_TYPE,
                    output: crate::compiler::meta::DEFINITIONS_TYPE,
                    span,
                },
            )?;
            self.attributes.insert(
                name,
                MetaCallable {
                    name,
                    params: params.iter().map(|(_, c)| *c).collect(),
                },
            );
        }
        Ok(())
    }

    fn validate_meta_callable_signature(
        &self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        ret: Option<&'bump Term<'bump>>,
        spec: MetaSignatureSpec<'_>,
    ) -> Result<(), Diagnostic> {
        let first_param = params.first().and_then(|(_, c)| *c);
        if !first_param.is_some_and(|ty| Self::is_meta_type_name(ty, spec.first)) {
            return Err(Diagnostic::with_span(
                format!(
                    "function `{name}` cannot be used as {}: first parameter must be {}",
                    spec.marker, spec.first
                ),
                spec.span,
            ));
        }
        if !ret.is_some_and(|ty| Self::is_meta_type_name(ty, spec.output)) {
            return Err(Diagnostic::with_span(
                format!(
                    "function `{name}` cannot be used as {}: return value must be {}",
                    spec.marker, spec.output
                ),
                spec.span,
            ));
        }
        Ok(())
    }

    pub(crate) fn is_meta_type_name(term: &Term<'_>, expected: &str) -> bool {
        match term {
            Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
                crate::config::canonical_builtin_name(name) == expected
            }
            Term::Annot(inner, _) | Term::Implicit(inner) => {
                Self::is_meta_type_name(inner, expected)
            }
            _ => false,
        }
    }

    fn process_def(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
        termination_claim: TerminationClaim<'bump>,
    ) -> Result<(), Diagnostic> {
        let name = self.codegen_attribute_target_name(name);
        let body = self.desugar_checked_def(params, m_ret, body)?;
        let semantics = SemanticQueries::new(self.checker.builtins());
        let universe = semantics.universe(&empty_ctx(), body);
        if self.definition_result_is_erased_universe(body)? {
            self.ensure_logic_data_refs_terminate(body, span.clone())?;
        }
        if universe == Some(Universe::UProp) {
            self.ensure_logic_data_refs_terminate(body, span.clone())?;
            self.validate_runtime_members_are_data(body)
                .map_err(|err| {
                    Self::wrap_diagnostic(format!("definition {name} failed"), err, span.clone())
                })?;
            if self.register_prop_definition(name, params, m_ret, body) {
                return Ok(());
            }
        }

        let has_erased_parameter = self.has_erased_parameter(params);
        let previous = if has_erased_parameter {
            self.env.insert(name, body)
        } else {
            self.env.insert(name, self.definition_signature(body))
        };
        let resolved_body = if has_erased_parameter {
            None
        } else {
            Some(self.try_resolve_all(body)?)
        };
        if let Some(resolved_body) = resolved_body
            && let Err(err) = self.checker.check(
                &empty_ctx(),
                resolved_body,
                self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
            )
        {
            self.restore_env_binding(name, previous);
            return Err(Self::wrap_diagnostic(
                format!("definition {name} failed"),
                err,
                span,
            ));
        }

        if !self.quiet {
            println!("[defined] {}", name);
        }
        self.verify_termination_claim(termination_claim, span.clone())?;
        self.record_data_termination(name, body, termination_claim);
        let stored_body = if body.is_constant() {
            resolved_body.unwrap_or_else(|| self.subst_top_level(body))
        } else {
            body
        };
        self.env.insert(name, stored_body);
        Ok(())
    }

    fn process_extern_def(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        ret: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        for (pname, constraint) in params {
            if constraint.is_none() {
                return Err(Diagnostic::with_span(
                    format!("extern parameter `{pname}` requires an explicit constraint"),
                    span,
                ));
            }
        }
        let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
        let ret = self.checker.desugar_with_names_context(ret, &names)?;
        let signature =
            params
                .iter()
                .enumerate()
                .rev()
                .try_fold(ret, |cod, (idx, &(pn, mc))| {
                    let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
                    let dom = self
                        .checker
                        .desugar_with_names_context(mc.expect("checked above"), &dom_env)?;
                    Ok::<_, Diagnostic>(self.arena.pi(pn, dom, cod))
                })?;
        let symbol = self.arena.global(name);
        let typed_symbol = self.arena.annot(symbol, signature);
        self.checker.add_extern(name, signature);
        self.mark_extern_terminating(name);
        self.env.insert(name, typed_symbol);
        if !self.quiet {
            println!("[extern] {}", name);
        }
        Ok(())
    }

    fn process_instance(
        &mut self,
        name: Name<'bump>,
        constraint: &'bump Term<'bump>,
        value: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        let resolved_constraint = self.checker.desugar_with_context(constraint)?;
        let resolved_value = self.resolve_instance_value(value, resolved_constraint)?;
        let resolved_value = self.attach_global_signatures(resolved_value);
        self.checker
            .check(&empty_ctx(), resolved_value, resolved_constraint)
            .map_err(|err| {
                Self::wrap_diagnostic(format!("instance {name} failed"), err, span.clone())
            })?;
        self.checker
            .add_instance(name, resolved_constraint, resolved_value);
        if !self.quiet {
            println!("[instance] {}", name);
        }
        Ok(())
    }

    fn restore_env_binding(&mut self, name: Name<'bump>, previous: Option<&'bump Term<'bump>>) {
        if let Some(prev) = previous {
            self.env.insert(name, prev);
        } else {
            self.env.remove(name);
        }
    }

    fn attach_global_signatures(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(term, &|node| {
            if let Term::Builtin(name) | Term::Global(name) = node
                && let Some(Term::Annot(_, signature)) = self.env.get(name).copied()
            {
                return Some(self.arena.annot(self.arena.global(name), signature));
            }
            None
        })
    }

    fn process_check(
        &self,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        let resolved_constraint = self.try_resolve_all(constraint)?;
        let resolved = self.try_resolve_all_with_expected(term, Some(resolved_constraint))?;
        if self.is_erased_universe_constraint(constraint)? {
            let logical_term = self.checker.desugar_with_context(term)?;
            self.ensure_logic_data_refs_terminate(logical_term, span.clone())?;
        }
        match self
            .checker
            .check(&empty_ctx(), resolved, resolved_constraint)
        {
            Err(err) => Err(Self::wrap_diagnostic("check failed", err, span)),
            Ok(_) => {
                if !self.quiet {
                    println!("[OK]");
                }
                Ok(())
            }
        }
    }

    fn process_theorem(
        &mut self,
        name: Name<'bump>,
        prop: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        let logical_prop = self.checker.desugar_with_context(prop)?;
        let logical_body = self.checker.desugar_with_context(body)?;
        self.ensure_logic_data_refs_terminate(logical_prop, span.clone())?;
        self.ensure_logic_data_refs_terminate(logical_body, span.clone())?;
        let resolved_prop = self.try_resolve_all(prop)?;
        let resolved_body = self.try_resolve_all_with_expected(body, Some(resolved_prop))?;
        match self
            .checker
            .check(&empty_ctx(), resolved_body, resolved_prop)
        {
            Err(err) => Err(Self::wrap_diagnostic("theorem check failed", err, span)),
            Ok(_) => {
                if !self.quiet {
                    println!("[theorem] {}", name);
                }
                self.env
                    .insert(name, self.arena.annot(resolved_body, resolved_prop));
                Ok(())
            }
        }
    }
}
