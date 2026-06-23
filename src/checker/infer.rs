//! Type-inference / constraint-checking subroutines for `TypeChecker`.

use crate::checker::TypeChecker;
use crate::checker::builtin::{LogicKind, check_builtin, logic_kind};
use crate::checker::context::{
    Context, add_refine, add_theorem, expand_constraint, extend_ctx, extend_ctx_term, lookup_refine,
};
use crate::config::{BUILTIN_BOOL, BUILTIN_DATA};
use crate::core::syntax::{Name, Term, Universe};
use crate::pretty::PrettyPrinter;

impl<'bump> TypeChecker<'bump> {
    /// Returns true if the term represents the universal "data" top type
    /// (either as `Builtin("data")` or `Universe(UData)`).
    pub(crate) fn is_data_like(t: &Term<'_>) -> bool {
        matches!(t, Term::Builtin(n) if *n == BUILTIN_DATA)
            || matches!(t, Term::Universe(Universe::UData))
    }

    /// Check an application: infer f's type (recursively through
    /// curried applications), check that the argument satisfies the
    /// domain, and that the result matches the constraint.
    pub(crate) fn check_app(
        &self,
        ctx: &Context<'bump>,
        f: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        // Check if f is a variant constructor
        let f_dsg = self.desugarer.desugar(f);
        if let Term::Builtin(name) = f_dsg {
            if let Some((uname, idx, field_specs)) = self.lookup_variant(name) {
                if field_specs.len() != 1 {
                    return Err(format!(
                        "Variant {} expects {} field(s), got 1",
                        name,
                        field_specs.len()
                    ));
                }
                let field_constraint = field_specs[0].1;
                self.check(ctx, a, field_constraint)?;
                let variant_term = self.arena.variant(uname, idx, self.arena.alloc_slice(&[a]));
                return self.check_by_constraint(ctx, variant_term, constraint);
            }
            // Check if f is a struct constructor (Name.mk)
            if let Some((sname, field_specs)) = self.lookup_struct_ctor(name) {
                if field_specs.len() != 1 {
                    return Err(format!(
                        "Struct constructor {}.mk expects {} field(s), got 1",
                        sname,
                        field_specs.len()
                    ));
                }
                let field_constraint = field_specs[0].1;
                self.check(ctx, a, field_constraint)?;
                let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&[a]));
                return self.check_by_constraint(ctx, sc, constraint);
            }
            // Check if f is a struct projector (Name.field)
            if let Some(idx) = self.lookup_struct_proj(name) {
                let proj = self.arena.struct_proj(a, idx);
                return self.check(ctx, proj, constraint);
            }
        }
        match self.infer_fun_type(ctx, f)? {
            Some(ty) => {
                let ty_norm = self.evaluator.whnf(ty)?;
                if let Term::Pi(_, a_dom, b_cod) = ty_norm {
                    self.check(ctx, a, a_dom)?;
                    self.check_domain_match(b_cod, constraint)?;
                    Ok(())
                } else {
                    Err(format!(
                        "Cannot apply argument to a non-function: expression has type {}",
                        PrettyPrinter::pretty(ty_norm)
                    ))
                }
            }
            None => {
                // No type information — check for undefined names first.
                let f_dsg = self.desugarer.desugar(f);
                if let Term::Builtin(name) = f_dsg
                    && check_builtin(name).is_none()
                    && lookup_refine(name, &self.table).is_none()
                {
                    return Err(format!("Undefined variable: {}", name));
                }
                let f_val = self.evaluator.whnf(f_dsg)?;
                let evald = self.evaluator.whnf(self.arena.app(f_val, a))?;
                self.check_by_constraint(ctx, evald, constraint)
            }
        }
    }

    /// Recursively infer the Pi type of a function expression.
    ///
    /// - `Annot(_, ty)` → use the annotation directly.
    /// - `App(f2, a2)` → infer f2's type, check a2 against the domain,
    ///   and return the codomain (handles curried applications).
    /// - `Var(i)`     → look up in the context.
    /// - Otherwise    → return `None` (no type information available).
    fn infer_fun_type(
        &self,
        ctx: &Context<'bump>,
        f: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, String> {
        let f_dsg = self.desugarer.desugar(f);
        match f_dsg {
            Term::Annot(_, ty) => Ok(Some(ty)),
            Term::App(f2, a2) => {
                let Some(f2_ty) = self.infer_fun_type(ctx, f2)? else {
                    return Ok(None);
                };
                let ty_norm = self.evaluator.whnf(f2_ty)?;
                match ty_norm {
                    Term::Pi(_, a_dom, b_cod) => {
                        self.check(ctx, a2, a_dom)?;
                        Ok(Some(b_cod))
                    }
                    _ => Ok(None),
                }
            }
            _ => {
                let f_val = self.evaluator.whnf(f_dsg)?;
                match f_val {
                    Term::Var(i) => Ok(ctx.lookup(*i)),
                    _ => Ok(None),
                }
            }
        }
    }

    pub(crate) fn check_var(
        &self,
        ctx: &Context<'bump>,
        i: usize,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let expected = ctx
            .lookup(i)
            .ok_or_else(|| format!("Unbound variable index: {}", i))?;
        let expected_val = self.evaluator.whnf(expected)?;
        let constraint_val = self.evaluator.whnf(constraint)?;
        if expected_val == constraint_val || self.is_refinement_of(expected_val, constraint_val) {
            Ok(())
        } else {
            Err(format!(
                "Type mismatch: variable is declared as {}, but is used where {} is expected",
                PrettyPrinter::pretty(expected_val),
                PrettyPrinter::pretty(constraint_val)
            ))
        }
    }

    pub(crate) fn check_if(
        &self,
        ctx: &Context<'bump>,
        cond: &'bump Term<'bump>,
        tbranch: &'bump Term<'bump>,
        fbranch: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let bool_name = self.arena.alloc_str(BUILTIN_BOOL);
        self.check(ctx, cond, self.arena.builtin(bool_name))?;
        let ctx_t = add_theorem("_", cond, ctx);
        let ctx_f = add_theorem("_", self.not_term(cond), ctx);
        self.check(&ctx_t, tbranch, constraint)?;
        self.check(&ctx_f, fbranch, constraint)
    }

    /// Check a match expression: verify scrutinee is a union type, check each branch.
    pub(crate) fn check_match(
        &self,
        ctx: &Context<'bump>,
        _scrutinee: &'bump Term<'bump>,
        branches: &'bump [(
            usize,
            &'bump [(Name<'bump>, &'bump Term<'bump>)],
            &'bump Term<'bump>,
        )],
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        // For each branch, bind payload variables and check the body
        for (_idx, binds, body) in branches.iter() {
            let mut branch_ctx = ctx.clone();
            // Bind payload variables in reverse order (innermost first)
            for (name, bind_constraint) in binds.iter().rev() {
                branch_ctx = branch_ctx.extend(name, bind_constraint);
            }
            self.check(&branch_ctx, body, constraint)?;
        }
        Ok(())
    }

    pub(crate) fn check_let(
        &self,
        ctx: &Context<'bump>,
        val: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        mconstr: Option<&'bump Term<'bump>>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        if let Some(c) = mconstr {
            self.check(ctx, val, c)?;
        }
        let new_ctx = extend_ctx_term(constraint, ctx);
        self.check(&new_ctx, body, constraint)
    }

    pub(crate) fn check_by_constraint(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        if let Term::Refine(name, parent, p) = constraint {
            let new_table = add_refine(name, parent, p, &self.table);
            let checker = Self::with_table(self.arena, &new_table);
            checker.check(ctx, term, parent)?;
            return self.prove_auto(ctx, term, p);
        }

        let norm = self.evaluator.whnf(constraint)?;
        match norm {
            Term::Builtin(name) => {
                // Check if term is a Variant — verify union name matches constraint
                if let Term::Variant(uname, _, _) = term {
                    if uname == name {
                        return Ok(());
                    }
                }
                if let Some(builtin_checker) = check_builtin(name) {
                    let evald = self.evaluator.whnf(term)?;
                    builtin_checker(evald)
                } else if let Some((parent, pred)) = lookup_refine(name, &self.table) {
                    self.check(ctx, term, parent)?;
                    self.prove_auto(ctx, term, pred)
                } else if self.lookup_union(name).is_some() {
                    // Union type — check if term is a Variant of this union
                    if let Term::Variant(uname, _, _) = term {
                        if uname == name {
                            Ok(())
                        } else {
                            Err(format!(
                                "Expected variant of {}, got variant of {}",
                                name, uname
                            ))
                        }
                    } else {
                        Err(format!(
                            "Expected a variant of {}, got {}",
                            name,
                            PrettyPrinter::pretty(term)
                        ))
                    }
                } else if self.lookup_struct(name).is_some() {
                    // Struct type — check if term is a StructCons of this struct
                    if let Term::StructCons(sname, _) = term {
                        if sname == name {
                            Ok(())
                        } else {
                            Err(format!("Expected struct {}, got struct {}", name, sname))
                        }
                    } else {
                        Err(format!(
                            "Expected a struct {}, got {}",
                            name,
                            PrettyPrinter::pretty(term)
                        ))
                    }
                } else {
                    Err(format!("Unknown builtin type: {}", name))
                }
            }
            Term::Pi("", a, b) => self.check_arrow(ctx, term, a, b),
            Term::Pi(name, a, b) => self.check_pi(ctx, term, name, a, b),
            Term::Universe(Universe::UData) => Ok(()),
            Term::Var(j) => Err(format!(
                "Variable {} is a value, not a type — cannot be used as a type constraint",
                j
            )),
            Term::App(app_and, a) => self.try_check_logical_op(ctx, term, app_and, a, norm),
            _ => {
                if let Some(result) = self.try_bool_constraint(term, norm) {
                    return result;
                }

                let cname = self.constraint_name(norm);
                if let Some((parent, pred)) = lookup_refine(cname, &self.table) {
                    self.check(ctx, term, parent)?;
                    self.prove_auto(ctx, term, pred)
                } else {
                    Err(format!(
                        "{} cannot be used as a type constraint",
                        PrettyPrinter::pretty(norm)
                    ))
                }
            }
        }
    }

    pub(crate) fn try_check_logical_op(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        head: &'bump Term<'bump>,
        arg: &'bump Term<'bump>,
        norm: &'bump Term<'bump>,
    ) -> Result<(), String> {
        // Single-arg case: (not A) — vacuous operators always succeed.
        if let Term::Builtin(name) = head {
            if logic_kind(name) == Some(LogicKind::Vacuous) {
                return Ok(());
            }
            return self.check_app_constraint(ctx, term, norm);
        }

        let Term::App(builtin, b) = head else {
            return self.check_app_constraint(ctx, term, norm);
        };
        let Term::Builtin(name) = *builtin else {
            return self.check_app_constraint(ctx, term, norm);
        };
        match logic_kind(name) {
            Some(LogicKind::Conj) => {
                self.check(ctx, term, arg)?;
                self.check(ctx, term, b)
            }
            Some(LogicKind::Disj) => self
                .check(ctx, term, arg)
                .or_else(|_| self.check(ctx, term, b)),
            Some(LogicKind::Vacuous) => Ok(()),
            None => self.check_app_constraint(ctx, term, norm),
        }
    }

    pub(crate) fn check_arrow(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> Result<(), String> {
        self.check_pi_impl(ctx, t, a, b, None)
    }

    pub(crate) fn check_pi(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        name: crate::core::syntax::Name<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> Result<(), String> {
        self.check_pi_impl(ctx, t, a, b, Some(name))
    }

    fn check_pi_impl(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
        name: Option<crate::core::syntax::Name<'bump>>,
    ) -> Result<(), String> {
        let t_val = self.evaluator.whnf(t)?;
        let Term::Lam(body) = t_val else {
            return Err(format!(
                "Expected a function (lambda), but got {}",
                PrettyPrinter::pretty(t_val)
            ));
        };
        let new_ctx = match name {
            Some(n) if !n.is_empty() => extend_ctx(n, a, ctx),
            _ => extend_ctx_term(a, ctx),
        };
        self.check(&new_ctx, body, b)
    }

    /// Try to satisfy a constraint by treating it as a boolean predicate.
    fn try_bool_constraint(
        &self,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Option<Result<(), String>> {
        let instantiated = self.subst_ref_param(term, constraint);
        let Ok(val) = self.evaluator.whnf(instantiated) else {
            return None;
        };
        match val {
            Term::LitBool(true) => Some(Ok(())),
            Term::LitBool(false) => Some(Err(format!(
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
    ) -> Result<(), String> {
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

        // Try to treat the constraint as a boolean predicate.
        if let Some(result) = self.try_bool_constraint(term, constraint) {
            return result;
        }

        Err(format!(
            "{} cannot be used as a type constraint",
            PrettyPrinter::pretty(constraint)
        ))
    }

    /// Compare two Pi types structurally (ignoring parameter names).
    pub(crate) fn check_pi_match(
        &self,
        annot: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
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
            (Term::Builtin(n1), Term::Builtin(n2)) if n1 == n2 => Ok(()),
            _ if Self::is_data_like(a) || Self::is_data_like(c) => Ok(()),
            _ if a == c => Ok(()),
            _ => Err(format!(
                "Type mismatch: expected {}, got {}",
                PrettyPrinter::pretty(constraint),
                PrettyPrinter::pretty(annot)
            )),
        }
    }

    /// Compare two domain types; contravariant: if the function's declared
    /// domain is `data` (the top type), any argument type is accepted.
    pub(crate) fn check_domain_match(
        &self,
        annot: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let a_val = self.evaluator.whnf(annot)?;
        let c_val = self.evaluator.whnf(constraint)?;
        let ok = a_val == c_val
            || self.is_refinement_of(c_val, a_val)
            || Self::is_data_like(c_val)
            || Self::is_data_like(a_val);
        if ok {
            Ok(())
        } else {
            Err(format!(
                "Argument type mismatch: expected {}, but argument has type {}",
                PrettyPrinter::pretty(a_val),
                PrettyPrinter::pretty(c_val)
            ))
        }
    }

    pub(crate) fn constraint_name<'a>(&self, t: &Term<'a>) -> &'a str {
        match t {
            Term::Builtin(n) => n,
            Term::Refine(n, _, _) => n,
            _ => "?",
        }
    }

    pub(crate) fn is_refinement_of(&self, t1: &'bump Term<'bump>, t2: &'bump Term<'bump>) -> bool {
        if t1 == t2 {
            return true;
        }
        // `data` is the universal supertype — every term is compatible with it.
        if Self::is_data_like(t2) {
            return true;
        }
        match t1 {
            Term::Refine(_, parent, _) => self.is_refinement_of(parent, t2),
            Term::Builtin(n) => lookup_refine(n, &self.table)
                .map(|(parent, _)| self.is_refinement_of(parent, t2))
                .unwrap_or(false),
            _ => false,
        }
    }

    /// Wrap a term in a boolean negation.
    pub(crate) fn not_term(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        let body = self.arena.if_then_else(
            self.arena.var(0),
            self.arena.lit_bool(false),
            self.arena.lit_bool(true),
        );
        self.arena.app(self.arena.lam(body), t)
    }

    /// Check a struct construction against a constraint.
    pub(crate) fn check_struct_cons(
        &self,
        ctx: &Context<'bump>,
        sname: Name<'bump>,
        field_values: &'bump [&'bump Term<'bump>],
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        // Look up the struct definition
        let sdef = self
            .lookup_struct(sname)
            .ok_or_else(|| format!("Unknown struct type: {}", sname))?;
        let Term::StructDef(_, fields) = sdef else {
            return Err(format!("{} is not a struct type", sname));
        };
        if field_values.len() != fields.len() {
            return Err(format!(
                "Struct {} expects {} field(s), got {}",
                sname,
                fields.len(),
                field_values.len()
            ));
        }
        // Check each field value against its constraint
        for (i, (fname, fconstraint)) in fields.iter().enumerate() {
            self.check(ctx, field_values[i], fconstraint)
                .map_err(|e| format!("In field '{}' of struct {}: {}", fname, sname, e))?;
        }
        // Now check the constructed struct against the target constraint
        self.check_by_constraint(ctx, self.arena.struct_cons(sname, field_values), constraint)
    }

    /// Check a struct field projection against a constraint.
    pub(crate) fn check_struct_proj(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        idx: usize,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        // First try to evaluate the subject to see if it's a StructCons.
        let subject_val = self.evaluator.whnf(subject)?;
        if let Term::StructCons(sname, field_values) = subject_val {
            // Subject is a concrete struct — get the field value
            if let Some(field_val) = field_values.get(idx) {
                return self.check(ctx, field_val, constraint);
            } else {
                return Err(format!("Struct {} has no field at index {}", sname, idx));
            }
        }
        // For variables, look up the type in the context
        if let Term::Var(i) = subject_val {
            if let Some(ty) = ctx.lookup(*i) {
                let ty_nf = self.evaluator.whnf(ty)?;
                if let Term::Builtin(sname) = ty_nf {
                    if let Some(sdef) = self.lookup_struct(sname) {
                        if let Term::StructDef(_, fields) = sdef {
                            if let Some((_, field_constraint)) = fields.get(idx) {
                                // The projection type is the field's constraint
                                return self.check_domain_match(field_constraint, constraint);
                            }
                        }
                    }
                }
            }
            return Err(format!("Variable has no struct type in context"));
        }
        // Subject is a literal or non-struct type — reject
        if matches!(
            subject_val,
            Term::LitInt(_) | Term::LitBool(_) | Term::LitStr(_) | Term::Lam(_)
        ) {
            return Err(format!(
                "Cannot project field from {}: expected a struct",
                PrettyPrinter::pretty(subject_val)
            ));
        }
        // Subject is not yet concretely known — accept (conservative)
        Ok(())
    }
}
