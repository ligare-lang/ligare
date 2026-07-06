use super::*;

impl<'bump> Compiler<'bump> {
    pub(super) fn method_call_app_spine(
        term: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, Name<'bump>, Vec<&'bump Term<'bump>>)> {
        let mut head = term;
        let mut args = Vec::new();
        while let Term::App(f, a) = head {
            args.push(*a);
            head = f;
        }
        args.reverse();
        if let Term::MethodCall(receiver, method) = head {
            Some((*receiver, *method, args))
        } else {
            None
        }
    }

    pub(super) fn operator_app_spine(
        term: &'bump Term<'bump>,
    ) -> Option<(PrimOp, &'bump Term<'bump>, &'bump Term<'bump>)> {
        let Term::App(f, rhs) = term else {
            return None;
        };
        let Term::App(head, lhs) = f else {
            return None;
        };
        let Term::PrimOp(op) = head else {
            return None;
        };
        Some((*op, *lhs, *rhs))
    }

    pub(super) fn primop_method_name(&self, op: PrimOp) -> Name<'bump> {
        self.arena.alloc_str(match op {
            PrimOp::Add => "add",
            PrimOp::Sub => "sub",
            PrimOp::Mul => "mul",
            PrimOp::Div => "div",
            PrimOp::Mod_ => "mod_",
            PrimOp::Eq => "eq",
            PrimOp::Lt => "lt",
            PrimOp::Gt => "gt",
            PrimOp::Le => "le",
            PrimOp::Ge => "ge",
            PrimOp::Neq => "neq",
        })
    }

    pub(super) fn infer_parser_receiver_constraint(
        &self,
        term: &'bump Term<'bump>,
        scope: &[MethodScopeEntry<'bump>],
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        if let Some(constraint) = self.infer_literal_or_value_constraint(term) {
            return Ok(Some(constraint));
        }
        match term {
            Term::Named(name) => {
                let env = self.method_scope_names(scope);
                for entry in scope.iter().rev() {
                    if entry.name == *name {
                        return entry
                            .constraint
                            .map(|constraint| {
                                self.checker.desugar_with_names_context(constraint, &env)
                            })
                            .transpose();
                    }
                }
                Ok(self.env.get(name).and_then(|def| {
                    if let Term::Annot(_, constraint) = def {
                        Some(*constraint)
                    } else {
                        None
                    }
                }))
            }
            Term::Annot(_, constraint) => Ok(Some(self.checker.desugar_with_context(constraint)?)),
            _ => Ok(None),
        }
    }

    pub(super) fn infer_literal_or_value_constraint(
        &self,
        term: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        match term {
            Term::LitInt(_) => Some(self.arena.builtin(self.arena.alloc_str("int"))),
            Term::LitBool(_) => Some(self.arena.builtin(self.arena.alloc_str("bool"))),
            Term::LitStr(_) => Some(self.arena.builtin(self.arena.alloc_str("str"))),
            Term::StructCons(name, _) | Term::Variant(name, _, _) => Some(self.arena.builtin(name)),
            Term::Annot(_, constraint) => Some(*constraint),
            Term::Named(name) | Term::Builtin(name) | Term::Global(name) => self
                .checker
                .lookup_variant(name)
                .and_then(|(enum_name, _, fields)| {
                    fields.is_empty().then(|| self.arena.builtin(enum_name))
                }),
            _ => None,
        }
    }

    pub(super) fn method_scope_names(&self, scope: &[MethodScopeEntry<'bump>]) -> Vec<&'bump str> {
        scope.iter().rev().map(|entry| entry.name).collect()
    }
}
