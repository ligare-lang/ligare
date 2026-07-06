use super::*;

impl<'bump> TypeChecker<'bump> {
    pub(crate) fn check_if(
        &self,
        ctx: &Context<'bump>,
        cond: &'bump Term<'bump>,
        tbranch: &'bump Term<'bump>,
        fbranch: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let bool_name = self.arena.alloc_str(BUILTIN_BOOL);
        self.check(ctx, cond, self.arena.builtin(bool_name))?;
        let ctx_t = add_theorem("_", cond, ctx);
        let ctx_f = add_theorem("_", self.not_term(cond), ctx);
        self.check(&ctx_t, tbranch, constraint)?;
        self.check(&ctx_f, fbranch, constraint)
    }

    pub(crate) fn check_match(
        &self,
        ctx: &Context<'bump>,
        scrutinee: &'bump Term<'bump>,
        branches: &'bump [MatchBranch<'bump>],
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let variant_constraints = self.match_variant_constraints(ctx, scrutinee)?;
        for (idx, binds, body) in branches.iter() {
            let mut branch_ctx = ctx.clone();
            let payload_constraints = variant_constraints
                .as_ref()
                .and_then(|variants| variants.get(*idx).copied());
            for (i, (name, fallback_constraint)) in binds.iter().enumerate().rev() {
                let bind_constraint = payload_constraints
                    .and_then(|fields| fields.get(i).map(|(_, c)| *c))
                    .unwrap_or(*fallback_constraint);
                branch_ctx = branch_ctx.extend(name, bind_constraint);
            }
            self.check(&branch_ctx, body, constraint)?;
        }
        Ok(())
    }

    fn match_variant_constraints(
        &self,
        ctx: &Context<'bump>,
        scrutinee: &'bump Term<'bump>,
    ) -> Result<Option<VariantPayloadConstraints<'bump>>, Diagnostic> {
        let scrutinee = self.desugar_with_context(scrutinee)?;
        let enum_name = match self.evaluator.whnf(scrutinee)? {
            Term::Variant(name, _, _) => Some(name),
            Term::Var(i) => match ctx
                .lookup(*i)
                .map(|ty| self.evaluator.whnf(ty))
                .transpose()?
            {
                Some(Term::Builtin(name) | Term::Global(name)) => Some(name),
                _ => None,
            },
            _ => None,
        };
        let Some(name) = enum_name else {
            return Ok(None);
        };
        Ok(self.lookup_enum(name).and_then(|(udef, _)| match udef {
            Term::EnumDef(_, variants) => {
                let fields: Vec<_> = variants.iter().map(|(_, f)| *f).collect();
                Some(self.arena.alloc_slice(&fields))
            }
            _ => None,
        }))
    }
}
