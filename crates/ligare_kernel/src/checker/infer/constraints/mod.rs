use super::*;

mod data;
mod equivalence;

impl<'bump> TypeChecker<'bump> {
    pub(crate) fn check_by_constraint(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if let Term::Implicit(inner) = constraint {
            return self.check_by_constraint(ctx, term, inner);
        }
        if let Term::Refine(name, parent, p) = constraint {
            let new_table = add_refine(name, parent, p, &self.table);
            let checker = Self::with_table(self.arena, &new_table);
            checker.check(ctx, term, parent)?;
            return self.prove_auto(ctx, term, p);
        }

        let norm = self.evaluator.whnf(constraint)?;
        let result = match norm {
            Term::Builtin(name) | Term::Global(name) => {
                if let Term::Variant(uname, _, _) = term
                    && crate::config::canonical_builtin_name(uname)
                        == crate::config::canonical_builtin_name(name)
                {
                    return Ok(());
                }
                if let Some(builtin_checker) = self.builtins.checker(name) {
                    let evald = self.evaluator.whnf(term)?;
                    builtin_checker(evald)
                } else if let Some((parent, pred)) = lookup_refine(name, &self.table) {
                    self.check(ctx, term, parent)?;
                    self.prove_auto(ctx, term, pred)
                } else if self.lookup_enum(name).is_some() {
                    self.check_enum_constraint(term, name)
                } else if self.lookup_struct(name).is_some() {
                    self.check_struct_constraint(term, name)
                } else {
                    Err(diag!("unknown constraint: {}", name))
                }
            }
            Term::Pi("", a, b) => self.check_arrow(ctx, term, a, b),
            Term::Pi(name, a, b) => self.check_pi(ctx, term, name, a, b),
            Term::Universe(Universe::UData) => Ok(()),
            Term::Var(j) => {
                if let Some(c) = ctx.lookup(*j) {
                    self.check(ctx, term, c)
                } else {
                    Err(diag!("unbound constraint param at index {}", *j))
                }
            }
            Term::App(head, a) => {
                let head_nf = self.evaluator.whnf(head)?;
                if matches!(head_nf, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_IO))
                {
                    self.check(ctx, term, a)
                } else if matches!(head_nf, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_PTR))
                {
                    let inferred = self.infer_binding_constraint(ctx, term)?;
                    self.check_domain_match(inferred, norm)
                } else if let Term::EnumDef(uname, _) = head_nf {
                    self.check_enum_constraint(term, uname)
                } else if let Term::StructDef(sname, _) = head_nf {
                    self.check_struct_constraint(term, sname)
                } else if let Term::Builtin(uname) | Term::Global(uname) = head_nf
                    && self.lookup_enum(uname).is_some()
                {
                    self.check_enum_constraint(term, uname)
                } else if let Term::Builtin(sname) | Term::Global(sname) = head_nf
                    && self.lookup_struct(sname).is_some()
                {
                    self.check_struct_constraint(term, sname)
                } else {
                    self.try_check_logical_op(ctx, term, head, a, norm)
                }
            }
            Term::EnumDef(uname, _) => self.check_enum_constraint(term, uname),
            Term::StructDef(sname, _) => self.check_struct_constraint(term, sname),
            _ => {
                if let Some(result) = self.try_bool_constraint(term, norm) {
                    result
                } else {
                    let cname = self.constraint_name(norm);
                    if let Some((parent, pred)) = lookup_refine(cname, &self.table) {
                        self.check(ctx, term, parent)?;
                        self.prove_auto(ctx, term, pred)
                    } else {
                        Err(diag!(
                            "cannot use {} as a constraint",
                            PrettyPrinter::pretty(norm)
                        ))
                    }
                }
            }
        };
        result.and_then(|_| self.check_universe_level(ctx, term, constraint))
    }

    pub(crate) fn check_universe_level(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if self.is_data_top_constraint(constraint)? {
            let semantics = SemanticQueries::new(&self.builtins);
            if semantics.universe(ctx, term) == Some(Universe::UData) {
                return Ok(());
            }
        }
        let term_level = self.term_level(ctx, term)?;
        let constraint_level = self.constraint_level_for_check(constraint)?;
        if term_level < constraint_level {
            Ok(())
        } else {
            Err(diag!(
                "宇宙层级错误：项层级 {} 不小于约束层级 {}",
                term_level,
                constraint_level
            ))
        }
    }

    fn is_data_top_constraint(&self, constraint: &'bump Term<'bump>) -> Result<bool, Diagnostic> {
        let constraint = Self::implicit_inner(constraint);
        if Self::is_data_like(constraint) {
            return Ok(true);
        }
        Ok(Self::is_data_like(self.evaluator.whnf(constraint)?))
    }

    pub(super) fn check_var_universe_level(
        &self,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let constraint_level = self.constraint_level_for_check(constraint)?;
        let term_level = constraint_level.saturating_sub(1);
        if term_level < constraint_level {
            Ok(())
        } else {
            Err(diag!(
                "宇宙层级错误：项层级 {} 不小于约束层级 {}",
                term_level,
                constraint_level
            ))
        }
    }

    fn term_level(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
    ) -> Result<u32, Diagnostic> {
        match term {
            Term::Var(i) => Ok(ctx
                .lookup(*i)
                .map(|constraint| self.constraint_level_for_check(constraint))
                .transpose()?
                .unwrap_or(1)
                .saturating_sub(1)),
            Term::Annot(inner, _) => self.term_level(ctx, inner),
            Term::ByProof(Some(inner), _) => self.term_level(ctx, inner),
            Term::Unsafe(inner) | Term::Pure(inner) => self.term_level(ctx, inner),
            Term::App(..)
            | Term::StructCons(..)
            | Term::Variant(..)
            | Term::IfThenElse(..)
            | Term::Match(..)
            | Term::StructProj(..) => {
                if let Ok(constraint) = self.infer_binding_constraint(ctx, term) {
                    Ok(self
                        .constraint_level_for_check(constraint)?
                        .saturating_sub(1))
                } else {
                    Ok(compute_level(term))
                }
            }
            Term::Builtin(name) | Term::Global(name) => {
                if let Some((parent, predicate)) = lookup_refine(name, &self.table) {
                    Ok(compute_level(self.arena.refine(name, parent, predicate)))
                } else if let Some((def, _)) =
                    self.lookup_enum(name).or_else(|| self.lookup_struct(name))
                {
                    Ok(compute_level(def))
                } else {
                    Ok(compute_level(term))
                }
            }
            _ => Ok(compute_level(term)),
        }
    }

    fn constraint_level_for_check(
        &self,
        constraint: &'bump Term<'bump>,
    ) -> Result<u32, Diagnostic> {
        let constraint = Self::implicit_inner(constraint);
        match constraint {
            Term::Refine(_, parent, _) => return self.constraint_level_for_check(parent),
            Term::Universe(Universe::UData | Universe::UProp) => return Ok(1),
            Term::Universe(Universe::UTheorem | Universe::UProof) => return Ok(2),
            Term::Builtin(name) | Term::Global(name)
                if crate::config::is_builtin_name(name, crate::config::BUILTIN_DATA) =>
            {
                return Ok(1);
            }
            Term::Builtin(name) | Term::Global(name)
                if crate::config::is_builtin_name(name, crate::config::BUILTIN_UNIT) =>
            {
                return Ok(1);
            }
            Term::Builtin(name) | Term::Global(name)
                if matches!(
                    crate::config::canonical_builtin_name(name),
                    crate::config::BUILTIN_PROP
                        | crate::config::BUILTIN_THEOREM
                        | crate::config::BUILTIN_PROOF
                ) =>
            {
                return Ok(2);
            }
            Term::Builtin(name) | Term::Global(name) => {
                if let Some((parent, _)) = lookup_refine(name, &self.table) {
                    return self.constraint_level_for_check(parent);
                }
                if let Some((def, _)) = self.lookup_enum(name).or_else(|| self.lookup_struct(name))
                {
                    return Ok(compute_level(def));
                }
            }
            Term::App(..) => {
                if let Some((name, args)) = self.constraint_app_name_and_args(constraint)
                    && let Some((def, _)) =
                        self.lookup_enum(name).or_else(|| self.lookup_struct(name))
                {
                    let arg_level = args.iter().map(|arg| compute_level(arg)).max().unwrap_or(0);
                    return Ok(compute_level(def).max(arg_level.saturating_add(1)));
                }
            }
            _ => {}
        }
        let norm = self.evaluator.whnf(constraint)?;
        if norm == constraint {
            Ok(compute_level(norm).max(1))
        } else {
            self.normalized_constraint_level_for_check(norm)
        }
    }

    fn normalized_constraint_level_for_check(
        &self,
        constraint: &'bump Term<'bump>,
    ) -> Result<u32, Diagnostic> {
        let constraint = Self::implicit_inner(constraint);
        match constraint {
            Term::Refine(_, parent, _) => self.constraint_level_for_check(parent),
            Term::Universe(Universe::UData | Universe::UProp) => Ok(1),
            Term::Universe(Universe::UTheorem | Universe::UProof) => Ok(2),
            Term::Builtin(name) | Term::Global(name)
                if crate::config::is_builtin_name(name, crate::config::BUILTIN_DATA) =>
            {
                Ok(1)
            }
            Term::Builtin(name) | Term::Global(name)
                if crate::config::is_builtin_name(name, crate::config::BUILTIN_UNIT) =>
            {
                Ok(1)
            }
            Term::Builtin(name) | Term::Global(name)
                if matches!(
                    crate::config::canonical_builtin_name(name),
                    crate::config::BUILTIN_PROP
                        | crate::config::BUILTIN_THEOREM
                        | crate::config::BUILTIN_PROOF
                ) =>
            {
                Ok(2)
            }
            Term::Builtin(name) | Term::Global(name) => {
                if let Some((parent, _)) = lookup_refine(name, &self.table) {
                    self.constraint_level_for_check(parent)
                } else if let Some((def, _)) =
                    self.lookup_enum(name).or_else(|| self.lookup_struct(name))
                {
                    Ok(compute_level(def))
                } else {
                    Ok(compute_level(constraint))
                }
            }
            Term::App(..) => {
                if let Some((name, args)) = self.constraint_app_name_and_args(constraint)
                    && let Some((def, _)) =
                        self.lookup_enum(name).or_else(|| self.lookup_struct(name))
                {
                    let arg_level = args.iter().map(|arg| compute_level(arg)).max().unwrap_or(0);
                    Ok(compute_level(def).max(arg_level.saturating_add(1)))
                } else {
                    Ok(compute_level(constraint).max(1))
                }
            }
            _ => Ok(compute_level(constraint).max(1)),
        }
    }

    fn constraint_app_name_and_args(
        &self,
        term: &'bump Term<'bump>,
    ) -> Option<(Name<'bump>, Vec<&'bump Term<'bump>>)> {
        let mut args = Vec::new();
        let mut current = term;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        match current {
            Term::Builtin(name) | Term::Global(name) => Some((*name, args)),
            _ => None,
        }
    }

    pub(crate) fn try_check_logical_op(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        head: &'bump Term<'bump>,
        arg: &'bump Term<'bump>,
        norm: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if let Term::Builtin(name) | Term::Global(name) = head {
            if self.builtins.logic_kind(name) == Some(LogicKind::Vacuous) {
                return Ok(());
            }
            if let Some(result) = self.try_check_named_constraint_app(ctx, term, name, norm) {
                return result;
            }
            return self.check_app_constraint(ctx, term, norm);
        }

        let Term::App(builtin, b) = head else {
            return self.check_app_constraint(ctx, term, norm);
        };
        let (Term::Builtin(name) | Term::Global(name)) = *builtin else {
            return self.check_app_constraint(ctx, term, norm);
        };
        match self.builtins.logic_kind(name) {
            Some(LogicKind::Conj) => {
                self.check(ctx, term, arg)?;
                self.check(ctx, term, b)
            }
            Some(LogicKind::Disj) => self
                .check(ctx, term, arg)
                .or_else(|_| self.check(ctx, term, b)),
            Some(LogicKind::Vacuous) => Ok(()),
            None => {
                if let Some(result) = self.try_check_named_constraint_app(ctx, term, name, norm) {
                    return result;
                }
                self.check_app_constraint(ctx, term, norm)
            }
        }
    }

    fn try_check_named_constraint_app(
        &self,
        _ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        name: &str,
        _norm: &'bump Term<'bump>,
    ) -> Option<Result<(), Diagnostic>> {
        if self.lookup_enum(name).is_some() {
            Some(self.check_enum_constraint(term, name))
        } else if self.lookup_struct(name).is_some() {
            Some(self.check_struct_constraint(term, name))
        } else {
            None
        }
    }

    pub(crate) fn check_arrow(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        self.check_pi_impl(ctx, t, a, b, None)
    }

    pub(crate) fn check_pi(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        name: crate::core::syntax::Name<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        self.check_pi_impl(ctx, t, a, b, Some(name))
    }

    fn check_pi_impl(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
        name: Option<crate::core::syntax::Name<'bump>>,
    ) -> Result<(), Diagnostic> {
        let t_val = self.evaluator.whnf(t)?;
        let Term::Lam(body) = t_val else {
            return Err(diag!(
                "expected term constrained by Pi, got {}",
                PrettyPrinter::pretty(t_val)
            ));
        };
        let new_ctx = match name {
            Some(n) if !n.is_empty() => extend_ctx(n, a, ctx),
            _ => extend_ctx_term(a, ctx),
        };
        self.check(&new_ctx, body, b)
    }

    fn try_bool_constraint(
        &self,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Option<Result<(), Diagnostic>> {
        let instantiated = self.subst_ref_param(term, constraint);
        let Ok(val) = self.evaluator.whnf(instantiated) else {
            return None;
        };
        match val {
            Term::LitBool(true) => Some(Ok(())),
            Term::LitBool(false) => Some(Err(diag!(
                "Constraint does not hold: {} does not satisfy {}",
                PrettyPrinter::pretty(term),
                PrettyPrinter::pretty(constraint)
            ))),
            _ => None,
        }
    }

    pub(crate) fn check_app_constraint(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if let Some(expanded) = expand_constraint(self.arena, &self.table, constraint) {
            return self.check(ctx, term, expanded);
        }

        if let Term::App(f, a) = constraint {
            let cname = self.constraint_name(f);
            if let Some((parent, body)) = lookup_refine(cname, &self.table)
                && Self::is_data_like(parent)
            {
                return self.check(ctx, term, self.arena.app(body, a));
            }
        }

        if let Some(result) = self.try_bool_constraint(term, constraint) {
            return result;
        }

        Err(diag!(
            "cannot use {} as a constraint",
            PrettyPrinter::pretty(constraint)
        ))
    }

    pub(crate) fn check_pi_match(
        &self,
        annot: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let a = self.evaluator.whnf(annot)?;
        let c = self.evaluator.whnf(constraint)?;
        match (a, c) {
            (Term::Pi(_, a1, b1), Term::Pi(_, a2, b2)) => {
                self.check_domain_match(a1, a2)?;
                self.check_pi_match(b1, b2)
            }
            (Term::Refine(_, parent, _), other) | (other, Term::Refine(_, parent, _)) => {
                self.check_pi_match(parent, other)
            }
            (Term::Builtin(n1) | Term::Global(n1), Term::Builtin(n2) | Term::Global(n2))
                if is_builtin_name(n1, crate::config::canonical_builtin_name(n2)) =>
            {
                Ok(())
            }
            _ if Self::is_data_like(a) || Self::is_data_like(c) => Ok(()),
            _ if a == c => Ok(()),
            _ => Err(diag!(
                "constraint mismatch: expected {}, got {}",
                PrettyPrinter::pretty(constraint),
                PrettyPrinter::pretty(annot)
            )),
        }
    }

    pub(crate) fn check_domain_match(
        &self,
        annot: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let a_val = self.evaluator.whnf(Self::implicit_inner(annot))?;
        let c_val = self.evaluator.whnf(Self::implicit_inner(constraint))?;
        let ok = a_val == c_val
            || Self::pi_equiv(a_val, c_val)
            || self.is_refinement_of(c_val, a_val)
            || Self::is_data_like(c_val)
            || Self::effect_inner(c_val).is_some_and(|inner| {
                a_val == inner
                    || Self::pi_equiv(a_val, inner)
                    || self.is_refinement_of(inner, a_val)
                    || self.named_constraint_equiv(a_val, inner)
            })
            || self.named_constraint_equiv(a_val, c_val);
        if ok {
            Ok(())
        } else {
            Err(diag!(
                "argument constraint: expected {}, got {}",
                PrettyPrinter::pretty(a_val),
                PrettyPrinter::pretty(c_val)
            ))
        }
    }
}
