use super::*;

type NamedStructTarget<'bump> = (
    Name<'bump>,
    Option<Vec<&'bump Term<'bump>>>,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
);

impl<'bump> Compiler<'bump> {
    pub(crate) fn elaborate_of_nat_literals(
        &self,
        term: &'bump Term<'bump>,
        ctx: &Context<'bump>,
        expected: Option<&'bump Term<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        match term {
            Term::LitInt(n) => {
                if let Some(expected) = expected
                    && let Some(lowered) = self.lower_of_nat_literal(*n, expected)?
                {
                    return Ok(lowered);
                }
                Ok(term)
            }
            Term::App(f, a) => {
                let f = self.elaborate_of_nat_literals(f, ctx, None)?;
                let arg_expected = self.explicit_app_domain(ctx, f);
                let a = self.elaborate_of_nat_literals(a, ctx, arg_expected)?;
                Ok(self.arena.app(f, a))
            }
            Term::Annot(inner, constraint) => {
                let constraint = self.elaborate_of_nat_literals(constraint, ctx, None)?;
                let inner = self.elaborate_of_nat_literals(inner, ctx, Some(constraint))?;
                Ok(self.arena.annot(inner, constraint))
            }
            Term::Lam(body) => {
                let (next_ctx, body_expected) = if let Some(expected) = expected {
                    match self.checker.evaluator.whnf(expected)? {
                        Term::Pi(_, domain, codomain) => (ctx.extend_term(domain), Some(*codomain)),
                        _ => (ctx.clone(), None),
                    }
                } else {
                    (ctx.clone(), None)
                };
                Ok(self.arena.lam(self.elaborate_of_nat_literals(
                    body,
                    &next_ctx,
                    body_expected,
                )?))
            }
            Term::Pi(name, domain, codomain) => {
                let domain = self.elaborate_of_nat_literals(domain, ctx, None)?;
                let next_ctx = ctx.extend(name, domain);
                let codomain = self.elaborate_of_nat_literals(codomain, &next_ctx, None)?;
                Ok(self.arena.pi(name, domain, codomain))
            }
            Term::Let(name, value, body, constraint) => {
                let constraint = constraint
                    .map(|c| self.elaborate_of_nat_literals(c, ctx, None))
                    .transpose()?;
                let value = self.elaborate_of_nat_literals(value, ctx, constraint)?;
                let binding_constraint =
                    constraint.or_else(|| self.checker.infer_binding_constraint(ctx, value).ok());
                let next_ctx = binding_constraint
                    .map(|c| ctx.extend(name, c))
                    .unwrap_or_else(|| ctx.clone());
                let body = self.elaborate_of_nat_literals(body, &next_ctx, expected)?;
                Ok(self.arena.let_(name, value, body, constraint))
            }
            Term::IfThenElse(cond, then_branch, else_branch) => Ok(self.arena.if_then_else(
                self.elaborate_of_nat_literals(cond, ctx, None)?,
                self.elaborate_of_nat_literals(then_branch, ctx, expected)?,
                self.elaborate_of_nat_literals(else_branch, ctx, expected)?,
            )),
            Term::ByProof(inner, tactics) => {
                let inner = inner
                    .map(|t| self.elaborate_of_nat_literals(t, ctx, expected))
                    .transpose()?;
                let tactics = tactics
                    .iter()
                    .map(|tactic| {
                        Ok(match tactic {
                            Tactic::Exact(t) => {
                                Tactic::Exact(self.elaborate_of_nat_literals(t, ctx, None)?)
                            }
                            Tactic::Apply(t) => {
                                Tactic::Apply(self.elaborate_of_nat_literals(t, ctx, None)?)
                            }
                            Tactic::Intro(n) => Tactic::Intro(*n),
                            Tactic::Have(n, t) => {
                                Tactic::Have(n, self.elaborate_of_nat_literals(t, ctx, None)?)
                            }
                            Tactic::Custom(n, args) => {
                                let args = args
                                    .iter()
                                    .map(|arg| self.elaborate_of_nat_literals(arg, ctx, None))
                                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                                Tactic::Custom(n, self.arena.alloc_slice(&args))
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.by_proof(inner, self.arena.alloc_slice(&tactics)))
            }
            Term::Refine(name, parent, predicate) => {
                let parent = self.elaborate_of_nat_literals(parent, ctx, None)?;
                let predicate =
                    self.elaborate_of_nat_literals(predicate, &ctx.extend(name, parent), None)?;
                Ok(self.arena.refine(name, parent, predicate))
            }
            Term::StructCons(name, fields) => {
                let field_constraints =
                    self.checker
                        .lookup_struct(name)
                        .and_then(|(def, _)| match def {
                            Term::StructDef(_, fields) => Some(*fields),
                            _ => None,
                        });
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(idx, field)| {
                        let expected = field_constraints.and_then(|constraints| {
                            constraints.get(idx).map(|(_, constraint)| *constraint)
                        });
                        self.elaborate_of_nat_literals(field, ctx, expected)
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .struct_cons(name, self.arena.alloc_slice(&fields)))
            }
            Term::NamedStructCons(name, fields) => {
                let (struct_name, type_args, struct_fields) =
                    self.resolve_named_struct_target(*name, expected)?;
                let values = self.elaborate_named_struct_fields(
                    struct_name,
                    struct_fields,
                    type_args.as_deref(),
                    fields,
                    ctx,
                )?;
                Ok(self
                    .arena
                    .struct_cons(struct_name, self.arena.alloc_slice(&values)))
            }
            Term::Variant(name, idx, payloads) => {
                let payload_constraints =
                    self.checker
                        .lookup_enum(name)
                        .and_then(|(def, _)| match def {
                            Term::EnumDef(_, variants) => {
                                variants.get(*idx).map(|(_, fields)| *fields)
                            }
                            _ => None,
                        });
                let payloads = payloads
                    .iter()
                    .enumerate()
                    .map(|(payload_idx, payload)| {
                        let expected = payload_constraints.and_then(|fields| {
                            fields.get(payload_idx).map(|(_, constraint)| *constraint)
                        });
                        self.elaborate_of_nat_literals(payload, ctx, expected)
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .variant(name, *idx, self.arena.alloc_slice(&payloads)))
            }
            Term::Match(scrutinee, branches) => {
                let scrutinee = self.elaborate_of_nat_literals(scrutinee, ctx, None)?;
                let branches = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let mut branch_ctx = ctx.clone();
                        for (name, constraint) in binds.iter().rev() {
                            branch_ctx = branch_ctx.extend(name, constraint);
                        }
                        Ok((
                            *idx,
                            *binds,
                            self.elaborate_of_nat_literals(body, &branch_ctx, expected)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .match_(scrutinee, self.arena.alloc_slice(&branches)))
            }
            Term::StructProj(subject, idx) => Ok(self
                .arena
                .struct_proj(self.elaborate_of_nat_literals(subject, ctx, None)?, *idx)),
            Term::Unsafe(inner) => Ok(self
                .arena
                .unsafe_(self.elaborate_of_nat_literals(inner, ctx, expected)?)),
            Term::Pure(inner) => Ok(self
                .arena
                .pure(self.elaborate_of_nat_literals(inner, ctx, expected)?)),
            Term::Implicit(inner) => Ok(self
                .arena
                .implicit(self.elaborate_of_nat_literals(inner, ctx, None)?)),
            Term::EnumDef(name, variants) => {
                let variants = variants
                    .iter()
                    .map(|(variant, fields)| {
                        let fields = fields
                            .iter()
                            .map(|(field, constraint)| {
                                Ok((
                                    *field,
                                    self.elaborate_of_nat_literals(constraint, ctx, None)?,
                                ))
                            })
                            .collect::<Result<Vec<_>, Diagnostic>>()?;
                        Ok((*variant, self.arena.alloc_slice(&fields)))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.enum_def(name, self.arena.alloc_slice(&variants)))
            }
            Term::StructDef(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field, constraint)| {
                        Ok((
                            *field,
                            self.elaborate_of_nat_literals(constraint, ctx, None)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.struct_def(name, self.arena.alloc_slice(&fields)))
            }
            Term::Quote(_) | Term::Splice(_) | Term::AutoProof | Term::RefParam => Ok(term),
            _ => Ok(term),
        }
    }

    fn explicit_app_domain(
        &self,
        ctx: &Context<'bump>,
        f: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let constraint = self.checker.infer_binding_constraint(ctx, f).ok()?;
        match self.checker.evaluator.whnf(constraint).ok()? {
            Term::Pi(_, domain, _) => Some(domain),
            _ => None,
        }
    }

    fn resolve_named_struct_target(
        &self,
        explicit_name: Option<Name<'bump>>,
        expected: Option<&'bump Term<'bump>>,
    ) -> Result<NamedStructTarget<'bump>, Diagnostic> {
        if let Some(name) = explicit_name {
            let (def, _) = self
                .checker
                .lookup_struct(name)
                .ok_or_else(|| Diagnostic::new(format!("unknown struct in initializer: {name}")))?;
            let Term::StructDef(actual_name, fields) = def else {
                return Err(Diagnostic::new(format!(
                    "{name} is not a struct constraint"
                )));
            };
            let type_args =
                expected.and_then(|expected| self.constraint_type_args_for(actual_name, expected));
            return Ok((*actual_name, type_args, *fields));
        }

        let Some(expected) = expected else {
            return Err(Diagnostic::new(
                "cannot infer struct type for initializer; add a constraint or use Type{...}"
                    .to_string(),
            ));
        };
        let Some((head, type_args)) =
            self.constraint_head_and_args(crate::checker::TypeChecker::implicit_inner(expected))
        else {
            return Err(Diagnostic::new(format!(
                "expected a struct constraint for initializer, got {}",
                crate::pretty::PrettyPrinter::pretty(expected)
            )));
        };
        let Some((def, _)) = self.checker.lookup_struct(head) else {
            return Err(Diagnostic::new(format!(
                "expected a struct constraint for initializer, got {}",
                crate::pretty::PrettyPrinter::pretty(expected)
            )));
        };
        let Term::StructDef(actual_name, fields) = def else {
            return Err(Diagnostic::new(format!(
                "expected a struct constraint for initializer, got {}",
                crate::pretty::PrettyPrinter::pretty(expected)
            )));
        };
        Ok((*actual_name, Some(type_args), *fields))
    }

    fn elaborate_named_struct_fields(
        &self,
        struct_name: Name<'bump>,
        struct_fields: &'bump [(Name<'bump>, &'bump Term<'bump>)],
        type_args: Option<&[&'bump Term<'bump>]>,
        named_fields: &'bump [(Name<'bump>, &'bump Term<'bump>)],
        ctx: &Context<'bump>,
    ) -> Result<Vec<&'bump Term<'bump>>, Diagnostic> {
        for (idx, (field_name, _)) in named_fields.iter().enumerate() {
            if named_fields[..idx]
                .iter()
                .any(|(seen_name, _)| seen_name == field_name)
            {
                return Err(Diagnostic::new(format!(
                    "struct {struct_name} initializer duplicates field `{field_name}`"
                )));
            }
            if !struct_fields.iter().any(|(name, _)| name == field_name) {
                return Err(Diagnostic::new(format!(
                    "struct {struct_name} has no field `{field_name}`"
                )));
            }
        }

        let mut ordered = Vec::with_capacity(struct_fields.len());
        for (field_name, field_constraint) in struct_fields.iter() {
            let Some((_, value)) = named_fields.iter().find(|(name, _)| name == field_name) else {
                return Err(Diagnostic::new(format!(
                    "struct {struct_name} initializer is missing field `{field_name}`"
                )));
            };
            let field_constraint = if let Some(type_args) = type_args {
                self.replace_generic_constraint_vars(field_constraint, type_args)
            } else {
                *field_constraint
            };
            ordered.push(self.elaborate_of_nat_literals(value, ctx, Some(field_constraint))?);
        }
        Ok(ordered)
    }

    fn constraint_type_args_for(
        &self,
        expected_name: Name<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Option<Vec<&'bump Term<'bump>>> {
        let mut args = Vec::new();
        let mut current = crate::checker::TypeChecker::implicit_inner(constraint);
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        match current {
            Term::Builtin(name) | Term::Global(name) if *name == expected_name => Some(args),
            _ => match self
                .checker
                .evaluator
                .whnf(crate::checker::TypeChecker::implicit_inner(constraint))
                .ok()?
            {
                Term::StructDef(name, _) if *name == expected_name => Some(args),
                _ => None,
            },
        }
    }

    fn replace_generic_constraint_vars(
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
            Term::Annot(inner, constraint) => self.arena.annot(
                self.replace_generic_constraint_vars_at(inner, type_args, depth),
                self.replace_generic_constraint_vars_at(constraint, type_args, depth),
            ),
            _ => term,
        }
    }

    fn lower_of_nat_literal(
        &self,
        value: i64,
        expected: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        let expected = self
            .checker
            .evaluator
            .whnf(crate::checker::TypeChecker::implicit_inner(expected))?;
        if self.constraint_accepts_raw_int(expected) {
            return Ok(None);
        }
        let Some(interface_name) = self.of_nat_interface_name() else {
            return Ok(None);
        };
        let wanted = self.arena.app(self.arena.global(interface_name), expected);
        let Some((_, instance)) = self.checker.lookup_instance(wanted)? else {
            return Ok(None);
        };
        let Some(field) = self.instance_field(instance, interface_name, "of_nat") else {
            return Ok(None);
        };
        Ok(Some(self.arena.app(field, self.arena.lit_int(value))))
    }

    fn constraint_accepts_raw_int(&self, expected: &'bump Term<'bump>) -> bool {
        let int = self.arena.builtin(self.arena.alloc_str("int"));
        matches!(expected, Term::Builtin(name) | Term::Global(name) if crate::config::is_builtin_name(name, BUILTIN_INT))
            || expected == int
            || self.checker.is_refinement_of(expected, int)
    }

    fn of_nat_interface_name(&self) -> Option<Name<'bump>> {
        self.checker
            .struct_table
            .iter()
            .find(|(name, _, _)| name.rsplit("::").next().unwrap_or(name) == "OfNat")
            .map(|(name, _, _)| *name)
    }

    fn instance_field(
        &self,
        instance: &'bump Term<'bump>,
        interface_name: Name<'bump>,
        field_name: &str,
    ) -> Option<&'bump Term<'bump>> {
        let proj_name = self
            .arena
            .alloc_str(&format!("{interface_name}.{field_name}"));
        let idx = self.checker.lookup_struct_proj(proj_name)?;
        let instance = match instance {
            Term::Annot(inner, _) => *inner,
            _ => instance,
        };
        match instance {
            Term::StructCons(_, values) => values.get(idx).copied(),
            _ => Some(self.arena.struct_proj(instance, idx)),
        }
    }

    pub(crate) fn fold_struct_projections(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::StructProj(subject, idx) = node
                && let Term::StructCons(_, values) = subject
                && values.iter().any(|value| Self::is_dictionary_field(value))
            {
                return values.get(*idx).copied();
            }
            None
        })
    }

    fn is_dictionary_field(term: &Term<'_>) -> bool {
        match term {
            Term::Lam(_) => true,
            Term::Annot(inner, constraint) => {
                matches!(constraint, Term::Pi(..)) || Self::is_dictionary_field(inner)
            }
            Term::Builtin(_) | Term::Global(_) => true,
            _ => false,
        }
    }

    pub fn resolve_variant_apps(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(t)
            && args.len() == field_specs.len()
        {
            let v = self
                .arena
                .variant(uname, idx, self.arena.alloc_slice(&args));
            return self.resolve_variant_apps(v);
        }
        self.arena.map(t, &|node| {
            if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(node)
                && args.len() == field_specs.len()
            {
                let v = self
                    .arena
                    .variant(uname, idx, self.arena.alloc_slice(&args));
                return Some(self.resolve_variant_apps(v));
            }
            None
        })
    }

    pub fn collect_variant_args(&self, t: &'bump Term<'bump>) -> Option<VariantWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Global(name) = current
            && let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
        {
            return Some((uname, idx, field_specs, args));
        }
        None
    }

    pub fn resolve_struct_ctors(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Some((sname, field_specs, args)) = self.collect_struct_args(t)
            && args.len() == field_specs.len()
        {
            let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
            return self.resolve_struct_ctors(sc);
        }
        self.arena.map(t, &|node| {
            if let Some((sname, field_specs, args)) = self.collect_struct_args(node)
                && args.len() == field_specs.len()
            {
                let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
                return Some(self.resolve_struct_ctors(sc));
            }
            None
        })
    }

    pub fn collect_struct_args(&self, t: &'bump Term<'bump>) -> Option<StructWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Global(name) = current
            && let Some((sname, field_specs)) = self.checker.lookup_struct_ctor(name)
        {
            return Some((sname, field_specs, args));
        }
        None
    }

    pub fn resolve_struct_projs(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::App(f, arg) = node
                && let Term::Builtin(name) | Term::Global(name) = f
                && let Some(idx) = self.checker.lookup_struct_proj(name)
            {
                let arg = self.resolve_struct_ctors(self.resolve_struct_projs(arg));
                return Some(self.arena.struct_proj(arg, idx));
            }
            None
        })
    }
}
