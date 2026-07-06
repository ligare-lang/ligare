use super::*;

impl<'bump> TypeChecker<'bump> {
    pub(crate) fn check_enum_constraint(
        &self,
        term: &'bump Term<'bump>,
        expected: &str,
    ) -> Result<(), Diagnostic> {
        if let Term::Variant(actual, _, _) = term {
            if crate::config::canonical_builtin_name(actual)
                == crate::config::canonical_builtin_name(expected)
            {
                Ok(())
            } else {
                Err(diag!(
                    "expected term constrained by {}, got variant of {}",
                    expected,
                    actual
                ))
            }
        } else {
            Err(diag!(
                "expected term constrained by {}, got {}",
                expected,
                PrettyPrinter::pretty(term)
            ))
        }
    }

    pub(crate) fn check_struct_constraint(
        &self,
        term: &'bump Term<'bump>,
        expected: &str,
    ) -> Result<(), Diagnostic> {
        if let Term::StructCons(actual, _) = term {
            if *actual == expected {
                Ok(())
            } else {
                Err(diag!(
                    "expected term constrained by {}, got struct {}",
                    expected,
                    actual
                ))
            }
        } else {
            Err(diag!(
                "expected term constrained by {}, got {}",
                expected,
                PrettyPrinter::pretty(term)
            ))
        }
    }

    pub(crate) fn is_enum_generic_param(&self, enum_name: &str, constraint: &Term<'bump>) -> bool {
        if let Some((_, type_params)) = self.lookup_enum(enum_name) {
            match constraint {
                Term::Var(i) => return *i < type_params.len(),
                Term::Builtin(name) | Term::Global(name) => {
                    return type_params.iter().any(|p| **p == **name);
                }
                _ => {}
            }
        }
        false
    }

    pub(crate) fn is_struct_generic_param(
        &self,
        struct_name: &str,
        constraint: &Term<'bump>,
    ) -> bool {
        if let Some((_, type_params)) = self.lookup_struct(struct_name) {
            match constraint {
                Term::Var(i) => return *i < type_params.len(),
                Term::Builtin(name) | Term::Global(name) => {
                    return type_params.iter().any(|p| **p == **name);
                }
                _ => {}
            }
        }
        false
    }

    pub(crate) fn check_struct_cons(
        &self,
        ctx: &Context<'bump>,
        sname: Name<'bump>,
        field_values: &'bump [&'bump Term<'bump>],
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let (sdef, _) = self
            .lookup_struct(sname)
            .ok_or_else(|| diag!("unknown struct: {}", sname))?;
        let Term::StructDef(_, fields) = sdef else {
            return Err(diag!("{} is not a struct", sname));
        };
        if field_values.len() != fields.len() {
            return Err(diag!(
                "{} expects {} field(s), got {}",
                sname,
                fields.len(),
                field_values.len()
            ));
        }
        let (_, type_params) = self
            .lookup_struct(sname)
            .ok_or_else(|| diag!("unknown struct: {}", sname))?;
        let type_args = self.constraint_type_args_for(sname, constraint);
        for (i, (fname, fconstraint)) in fields.iter().enumerate() {
            let fconstraint = if let Some(type_args) = type_args.as_deref() {
                self.replace_generic_constraint_vars(fconstraint, type_args)
            } else {
                fconstraint
            };
            if Self::is_direct_prop_runtime_member(fconstraint) {
                return Err(Diagnostic::new(format!(
                    "data struct {} field '{}' cannot use prop/theorem/proof as a runtime member",
                    sname, fname
                )));
            }
            if type_args.is_none() && self.is_generic_param(type_params, fconstraint) {
                continue;
            }
            self.check(ctx, field_values[i], fconstraint).map_err(|e| {
                Diagnostic::new(format!("struct {} field '{}': {}", sname, fname, e))
            })?;
        }
        self.check_by_constraint(ctx, self.arena.struct_cons(sname, field_values), constraint)
    }

    pub(crate) fn check_variant(
        &self,
        ctx: &Context<'bump>,
        uname: Name<'bump>,
        idx: usize,
        payloads: &'bump [&'bump Term<'bump>],
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let (udef, type_params) = self
            .lookup_enum(uname)
            .ok_or_else(|| diag!("unknown enum: {}", uname))?;
        let Term::EnumDef(_, variants) = udef else {
            return Err(diag!("{} is not an enum", uname));
        };
        let (vname, fields) = variants
            .get(idx)
            .ok_or_else(|| diag!("enum {}: no variant at index {}", uname, idx))?;
        if payloads.len() != fields.len() {
            return Err(diag!(
                "variant {} expects {} field(s), got {}",
                vname,
                fields.len(),
                payloads.len()
            ));
        }
        let type_args = self.constraint_type_args_for(uname, constraint);
        for (i, (fname, fconstraint)) in fields.iter().enumerate() {
            let fconstraint = if let Some(type_args) = type_args.as_deref() {
                self.replace_generic_constraint_vars(fconstraint, type_args)
            } else {
                *fconstraint
            };
            if Self::is_direct_prop_runtime_member(fconstraint) {
                return Err(Diagnostic::new(format!(
                    "data enum {} variant {} field '{}' cannot use prop/theorem/proof as a runtime member",
                    uname, vname, fname
                )));
            }
            if type_args.is_none() && self.is_generic_param(type_params, fconstraint) {
                continue;
            }
            self.check(ctx, payloads[i], fconstraint).map_err(|e| {
                Diagnostic::new(format!("variant {} field '{}': {}", vname, fname, e))
            })?;
        }
        self.check_by_constraint(ctx, self.arena.variant(uname, idx, payloads), constraint)
    }

    fn is_generic_param(&self, type_params: &[Name<'bump>], constraint: &Term<'bump>) -> bool {
        match constraint {
            Term::Var(i) => *i < type_params.len(),
            Term::Builtin(name) | Term::Global(name) => type_params.iter().any(|p| **p == **name),
            _ => false,
        }
    }

    fn is_direct_prop_runtime_member(term: &Term<'_>) -> bool {
        match term {
            Term::Builtin(name) | Term::Global(name) => matches!(
                crate::config::canonical_builtin_name(name),
                crate::config::BUILTIN_PROP
                    | crate::config::BUILTIN_THEOREM
                    | crate::config::BUILTIN_PROOF
            ),
            Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
            Term::Implicit(inner) | Term::Annot(inner, _) => {
                Self::is_direct_prop_runtime_member(inner)
            }
            _ => false,
        }
    }

    pub(crate) fn constraint_type_args_for(
        &self,
        expected_name: Name<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Option<Vec<&'bump Term<'bump>>> {
        let mut args = Vec::new();
        let mut current = Self::implicit_inner(constraint);
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        match current {
            Term::Builtin(name) | Term::Global(name) if *name == expected_name => Some(args),
            _ => match self.evaluator.whnf(Self::implicit_inner(constraint)).ok()? {
                Term::EnumDef(name, _) | Term::StructDef(name, _) if *name == expected_name => {
                    Some(args)
                }
                _ => None,
            },
        }
    }

    pub(crate) fn replace_generic_constraint_vars(
        &self,
        term: &'bump Term<'bump>,
        type_args: &[&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        self.replace_generic_constraint_vars_at(term, type_args, 0)
    }

    fn replace_generic_constraint_vars_at(
        &self,
        term: &'bump Term<'bump>,
        type_args: &[&'bump Term<'bump>],
        depth: usize,
    ) -> &'bump Term<'bump> {
        match term {
            Term::Var(i) if *i >= depth && (*i - depth) < type_args.len() => {
                type_args[type_args.len() - 1 - (*i - depth)]
            }
            Term::App(f, a) => self.arena.app(
                self.replace_generic_constraint_vars_at(f, type_args, depth),
                self.replace_generic_constraint_vars_at(a, type_args, depth),
            ),
            Term::Implicit(inner) => self
                .arena
                .implicit(self.replace_generic_constraint_vars_at(inner, type_args, depth)),
            Term::Pi(name, a, b) => self.arena.pi(
                name,
                self.replace_generic_constraint_vars_at(a, type_args, depth),
                self.replace_generic_constraint_vars_at(b, type_args, depth + 1),
            ),
            Term::Annot(inner, c) => self.arena.annot(
                self.replace_generic_constraint_vars_at(inner, type_args, depth),
                self.replace_generic_constraint_vars_at(c, type_args, depth),
            ),
            _ => term,
        }
    }

    pub(crate) fn check_struct_proj(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        idx: usize,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let subject_val = self.evaluator.whnf(subject)?;
        if let Term::StructCons(sname, field_values) = subject_val {
            if let Some(field_val) = field_values.get(idx) {
                return self.check(ctx, field_val, constraint);
            } else {
                return Err(diag!("struct {}: no field at index {}", sname, idx));
            }
        }
        if let Term::Var(i) = subject_val {
            if let Some(ty) = ctx.lookup(*i) {
                let ty_nf = self.evaluator.whnf(ty)?;
                if let Term::Builtin(sname) | Term::Global(sname) = ty_nf
                    && let Some((sdef, _)) = self.lookup_struct(sname)
                    && let Term::StructDef(_, fields) = sdef
                    && let Some((_, field_constraint)) = fields.get(idx)
                {
                    return self.check_domain_match(field_constraint, constraint);
                }
            }
            return Err(Diagnostic::new("term has no known struct constraint"));
        }
        if matches!(
            subject_val,
            Term::LitInt(_) | Term::LitBool(_) | Term::LitStr(_) | Term::Lam(_)
        ) {
            return Err(diag!(
                "cannot project from {}: term is not a struct construction",
                PrettyPrinter::pretty(subject_val)
            ));
        }
        Err(diag!(
            "cannot project field {} from {}: term has no known struct constraint",
            idx,
            PrettyPrinter::pretty(subject_val)
        ))
    }
}
