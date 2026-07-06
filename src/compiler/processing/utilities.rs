use super::*;

impl<'bump> Compiler<'bump> {
    pub(crate) fn register_operator_intrinsics(&mut self) {
        self.register_intrinsic_binop("std::primitive::int_add", PrimOp::Add, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_sub", PrimOp::Sub, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_mul", PrimOp::Mul, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_div", PrimOp::Div, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_mod", PrimOp::Mod_, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_eq", PrimOp::Eq, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_lt", PrimOp::Lt, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_gt", PrimOp::Gt, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_le", PrimOp::Le, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_ge", PrimOp::Ge, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_neq", PrimOp::Neq, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::str_add", PrimOp::Add, "str", "str", "str");
    }

    fn register_intrinsic_binop(
        &mut self,
        name: &'static str,
        op: PrimOp,
        left: &str,
        right: &str,
        ret: &str,
    ) {
        let left = self.arena.builtin(self.arena.alloc_str(left));
        let right = self.arena.builtin(self.arena.alloc_str(right));
        let ret = self.arena.builtin(self.arena.alloc_str(ret));
        let sig = self.arena.pi(
            self.arena.alloc_str(""),
            left,
            self.arena.pi(self.arena.alloc_str(""), right, ret),
        );
        self.env.insert(
            self.arena.alloc_str(name),
            self.arena.annot(self.arena.prim_op(op), sig),
        );
    }

    pub(super) fn validate_runtime_members_are_data(
        &self,
        body: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        match body {
            Term::EnumDef(enum_name, variants) => {
                for (variant_name, fields) in variants.iter() {
                    for (field_name, constraint) in fields.iter() {
                        if Self::is_direct_prop_runtime_member(constraint) {
                            return Err(Diagnostic::new(format!(
                                "data enum {} variant {} field '{}' cannot use prop/theorem/proof as a runtime member",
                                enum_name, variant_name, field_name
                            )));
                        }
                    }
                }
            }
            Term::StructDef(struct_name, fields) => {
                for (field_name, constraint) in fields.iter() {
                    if Self::is_direct_prop_runtime_member(constraint) {
                        return Err(Diagnostic::new(format!(
                            "data struct {} field '{}' cannot use prop/theorem/proof as a runtime member",
                            struct_name, field_name
                        )));
                    }
                }
            }
            Term::Annot(inner, _) => self.validate_runtime_members_are_data(inner)?,
            _ => {}
        }
        Ok(())
    }

    fn is_direct_prop_runtime_member(term: &Term<'_>) -> bool {
        match term {
            Term::Builtin(name) | Term::Global(name) | Term::Named(name) => matches!(
                canonical_builtin_name(name),
                BUILTIN_PROP | BUILTIN_THEOREM | BUILTIN_PROOF
            ),
            Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
            Term::Implicit(inner) | Term::Annot(inner, _) => {
                Self::is_direct_prop_runtime_member(inner)
            }
            _ => false,
        }
    }

    pub(super) fn has_erased_parameter(
        &self,
        params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
    ) -> bool {
        let semantics = SemanticQueries::new(self.checker.builtins());
        params.iter().any(|(_, c)| {
            c.is_some_and(|constraint| semantics.is_erased_parameter_constraint(constraint))
        })
    }

    pub(super) fn definition_signature(&self, body: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match body {
            Term::Annot(_, constraint) => {
                let stub = self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA));
                self.arena.annot(stub, constraint)
            }
            _ => body,
        }
    }

    pub(super) fn refinement_parts(
        body: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
        match body {
            Term::Refine(_, parent, predicate) => Some((*parent, *predicate)),
            Term::Annot(inner, _) => Self::refinement_parts(inner),
            _ => None,
        }
    }

    pub(crate) fn contains_do(term: &Term<'_>) -> bool {
        match term {
            Term::Do(_) => true,
            Term::Unsafe(inner) | Term::Pure(inner) => Self::contains_do(inner),
            Term::App(f, a) => Self::contains_do(f) || Self::contains_do(a),
            Term::NamedLam(_, body) | Term::Lam(body) => Self::contains_do(body),
            Term::Pi(_, a, b) => Self::contains_do(a) || Self::contains_do(b),
            Term::Let(_, val, body, mc) => {
                Self::contains_do(val)
                    || Self::contains_do(body)
                    || mc.is_some_and(Self::contains_do)
            }
            Term::IfThenElse(c, t, f) => {
                Self::contains_do(c) || Self::contains_do(t) || Self::contains_do(f)
            }
            Term::Refine(_, parent, pred) => Self::contains_do(parent) || Self::contains_do(pred),
            Term::Annot(inner, constraint) => {
                Self::contains_do(inner) || Self::contains_do(constraint)
            }
            Term::ByProof(inner, tactics) => {
                inner.is_some_and(Self::contains_do)
                    || tactics.iter().any(|t| match t {
                        crate::core::syntax::Tactic::Exact(t)
                        | crate::core::syntax::Tactic::Apply(t)
                        | crate::core::syntax::Tactic::Have(_, t) => Self::contains_do(t),
                        crate::core::syntax::Tactic::Intro(_) => false,
                        crate::core::syntax::Tactic::Custom(_, args) => {
                            args.iter().any(|arg| Self::contains_do(arg))
                        }
                    })
            }
            Term::EnumDef(_, variants) => variants.iter().any(|(_, fields)| {
                fields
                    .iter()
                    .any(|(_, constraint)| Self::contains_do(constraint))
            }),
            Term::Variant(_, _, payloads) | Term::StructCons(_, payloads) => {
                payloads.iter().any(|t| Self::contains_do(t))
            }
            Term::Match(scrut, branches) => {
                Self::contains_do(scrut)
                    || branches.iter().any(|(_, binds, body)| {
                        Self::contains_do(body)
                            || binds
                                .iter()
                                .any(|(_, constraint)| Self::contains_do(constraint))
                    })
            }
            Term::NamedMatch(scrut, branches) => {
                Self::contains_do(scrut)
                    || branches.iter().any(|(_, binds, body)| {
                        Self::contains_do(body)
                            || binds
                                .iter()
                                .any(|(_, constraint)| Self::contains_do(constraint))
                    })
            }
            Term::StructDef(_, fields) => fields.iter().any(|(_, c)| Self::contains_do(c)),
            Term::StructProj(subject, _) => Self::contains_do(subject),
            Term::MethodCall(subject, _) => Self::contains_do(subject),
            _ => false,
        }
    }

    pub(crate) fn codegen_attribute_target_name(&self, name: Name<'bump>) -> Name<'bump> {
        name.strip_prefix(GLOBAL_ALLOCATOR_NAME_PREFIX)
            .map(|stripped| self.arena.alloc_str(stripped))
            .unwrap_or(name)
    }

    pub(super) fn is_erased_universe_constraint(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<bool, Diagnostic> {
        let term = self.checker.desugar_with_context(term)?;
        Ok(match term {
            Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
            Term::Builtin(name) | Term::Global(name) => matches!(
                crate::config::canonical_builtin_name(name),
                crate::config::BUILTIN_PROP
                    | crate::config::BUILTIN_THEOREM
                    | crate::config::BUILTIN_PROOF
            ),
            _ => false,
        })
    }

    pub(super) fn definition_result_is_erased_universe(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<bool, Diagnostic> {
        let Some(result) = Self::definition_result_constraint(term) else {
            return Ok(false);
        };
        self.is_erased_universe_constraint(result)
    }

    fn definition_result_constraint(term: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        let Term::Annot(_, constraint) = term else {
            return None;
        };
        let mut result = *constraint;
        while let Term::Pi(_, _, codomain) = result {
            result = codomain;
        }
        Some(result)
    }

    pub(crate) fn wrap_diagnostic(
        prefix: impl Into<String>,
        mut err: Diagnostic,
        fallback_span: std::ops::Range<usize>,
    ) -> Diagnostic {
        err.message = format!("{}: {}", prefix.into(), err.message);
        if err.span.is_none() {
            err.span = Some(fallback_span);
        }
        err
    }
}
