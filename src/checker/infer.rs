//! Constraint inference and checking subroutines for `TypeChecker`.

use crate::checker::TypeChecker;
use crate::checker::builtin::LogicKind;
use crate::checker::context::{
    Context, add_refine, add_theorem, expand_constraint, extend_ctx, extend_ctx_term, lookup_refine,
};
use crate::config::{BUILTIN_BOOL, BUILTIN_DATA, BUILTIN_IO, BUILTIN_PTR, BUILTIN_PTR_CAST};
use crate::core::syntax::{MatchBranch, Name, PrimOp, Term, Universe};
use crate::diagnostic::Diagnostic;
use crate::pretty::PrettyPrinter;

type VariantPayloadConstraints<'bump> = &'bump [&'bump [(Name<'bump>, &'bump Term<'bump>)]];

macro_rules! diag {
    ($($arg:tt)*) => {
        Diagnostic::new(format!($($arg)*))
    };
}

impl<'bump> TypeChecker<'bump> {
    /// Returns true if the term represents the universal `data` constraint
    /// (either as `Builtin("data")` or `Universe(UData)`).
    pub(crate) fn is_data_like(t: &Term<'_>) -> bool {
        matches!(t, Term::Builtin(n) if *n == BUILTIN_DATA)
            || matches!(t, Term::Universe(Universe::UData))
    }

    /// Check an application: infer f's Pi constraint (recursively through
    /// curried applications), check that the argument satisfies the
    /// domain, and that the result matches the constraint.
    pub(crate) fn check_app(
        &self,
        ctx: &Context<'bump>,
        f: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if let Some(target) = self.ptr_cast_target(f)? {
            return self.check_ptr_cast(ctx, target, a, constraint);
        }
        if let Some(name) = self.extern_head_name(f)?
            && self.unsafe_depth == 0
        {
            return Err(diag!(
                "call to external function `{}` requires an unsafe context",
                name
            ));
        }
        // Check if f is a variant constructor
        let f_dsg = self.desugar_with_context(f)?;
        if let Term::Builtin(name) | Term::Global(name) = f_dsg {
            if let Some((uname, idx, field_specs)) = self.lookup_variant(name) {
                if field_specs.len() != 1 {
                    return Err(diag!(
                        "Variant {} expects {} field(s), got 1",
                        name,
                        field_specs.len()
                    ));
                }
                let field_constraint = field_specs[0].1;
                // If the field constraint is a generic parameter of the union,
                // skip the field check — the overall constraint check below
                // will verify the variant belongs to the right union.
                if !self.is_union_generic_param(uname, field_constraint) {
                    self.check(ctx, a, field_constraint)?;
                }
                let variant_term = self.arena.variant(uname, idx, self.arena.alloc_slice(&[a]));
                return self.check_by_constraint(ctx, variant_term, constraint);
            }
            // Check if f is a struct constructor (Name.mk)
            if let Some((sname, field_specs)) = self.lookup_struct_ctor(name) {
                if field_specs.len() != 1 {
                    return Err(diag!(
                        "Struct constructor {}.mk expects {} field(s), got 1",
                        sname,
                        field_specs.len()
                    ));
                }
                let field_constraint = field_specs[0].1;
                // If the field constraint is a generic parameter of the struct,
                // skip the field check.
                if !self.is_struct_generic_param(sname, field_constraint) {
                    self.check(ctx, a, field_constraint)?;
                }
                let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&[a]));
                return self.check_by_constraint(ctx, sc, constraint);
            }
            // Check if f is a struct projector (Name.field)
            if let Some(idx) = self.lookup_struct_proj(name) {
                let proj = self.arena.struct_proj(a, idx);
                return self.check(ctx, proj, constraint);
            }
            if self.lookup_extern(name).is_some() && self.unsafe_depth == 0 {
                return Err(diag!(
                    "call to external function `{}` requires an unsafe context",
                    name
                ));
            }
        }
        if let Term::App(prim, first) = f_dsg
            && let Term::PrimOp(op) = prim
        {
            return self.check_primop_app(ctx, *op, first, a, constraint);
        }
        match self.infer_pi_constraint(ctx, f)? {
            Some(ty) => {
                let pi_constraint = self.evaluator.whnf(ty)?;
                if let Term::Pi(_, a_dom, b_cod) = pi_constraint {
                    if Self::is_implicit_constraint(a_dom) {
                        if self.is_implicit_meta_constraint(a_dom) {
                            let inferred = self.infer_binding_constraint(ctx, a)?;
                            let f_with_inferred = self.arena.app(f, inferred);
                            return self.check_app(ctx, f_with_inferred, a, constraint);
                        }
                        let Some((instance_name, instance)) = self.lookup_instance(a_dom)? else {
                            return Err(diag!(
                                "missing implicit instance for {}",
                                PrettyPrinter::pretty(Self::implicit_inner(a_dom))
                            ));
                        };
                        let f_with_instance = self.arena.app(f, instance);
                        let result = self.check_app(ctx, f_with_instance, a, constraint);
                        return result.map_err(|err| {
                            diag!(
                                "while applying implicit instance `{}`: {}",
                                instance_name,
                                err
                            )
                        });
                    }
                    self.check(ctx, a, a_dom)?;
                    // Substitute the argument into the codomain to get the
                    // actual result constraint. This matters when the
                    // codomain depends on the parameter.
                    let sub = crate::core::debruijn::SubstitutionContext::new(self.arena);
                    let result_constraint = sub.instantiate_pi(a, b_cod);
                    self.check_domain_match(result_constraint, constraint)?;
                    Ok(())
                } else {
                    Err(diag!(
                        "application head is not constrained by a Pi term: {}",
                        PrettyPrinter::pretty(pi_constraint)
                    ))
                }
            }
            None => {
                // No Pi constraint information — check for undefined names first.
                let f_dsg = self.desugar_with_context(f)?;
                if let Term::Builtin(name) | Term::Global(name) = f_dsg
                    && self.builtins.checker(name).is_none()
                    && lookup_refine(name, &self.table).is_none()
                {
                    return Err(diag!("unbound: {}", name));
                }
                let f_val = self.evaluator.whnf(f_dsg)?;
                let evald = self.evaluator.whnf(self.arena.app(f_val, a))?;
                self.check_by_constraint(ctx, evald, constraint)
            }
        }
    }

    fn extern_head_name(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<Option<Name<'bump>>, Diagnostic> {
        let mut head = self.desugar_with_context(term)?;
        loop {
            match head {
                Term::App(f, _) => head = f,
                Term::Annot(inner, _) => head = inner,
                Term::Unsafe(inner) => head = inner,
                Term::Builtin(name) | Term::Global(name) if self.lookup_extern(name).is_some() => {
                    return Ok(Some(*name));
                }
                _ => return Ok(None),
            }
        }
    }

    fn check_primop_app(
        &self,
        ctx: &Context<'bump>,
        op: PrimOp,
        first: &'bump Term<'bump>,
        second: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let int = self.arena.builtin(self.arena.alloc_str("int"));
        if op == PrimOp::Add {
            let str_ty = self.arena.builtin(self.arena.alloc_str("str"));
            if self.check(ctx, first, str_ty).is_ok() && self.check(ctx, second, str_ty).is_ok() {
                self.check_domain_match(str_ty, constraint)?;
                let term = self
                    .arena
                    .app(self.arena.app(self.arena.prim_op(op), first), second);
                return self
                    .check_by_constraint(ctx, term, constraint)
                    .or_else(|err| {
                        if self.result_constraint_satisfies_constraint(str_ty, constraint) {
                            Ok(())
                        } else {
                            Err(err)
                        }
                    });
            }
        }
        self.check(ctx, first, int)?;
        self.check(ctx, second, int)?;
        let result_ty = match op {
            PrimOp::Add | PrimOp::Sub | PrimOp::Mul | PrimOp::Div | PrimOp::Mod_ => int,
            PrimOp::Eq | PrimOp::Lt | PrimOp::Gt | PrimOp::Le | PrimOp::Ge | PrimOp::Neq => {
                self.arena.builtin(self.arena.alloc_str(BUILTIN_BOOL))
            }
        };
        self.check_domain_match(result_ty, constraint)?;
        let term = self
            .arena
            .app(self.arena.app(self.arena.prim_op(op), first), second);
        self.check_by_constraint(ctx, term, constraint)
            .or_else(|err| {
                if self.result_constraint_satisfies_constraint(result_ty, constraint) {
                    Ok(())
                } else {
                    Err(err)
                }
            })
    }

    fn result_constraint_satisfies_constraint(
        &self,
        result_ty: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> bool {
        let Ok(c_val) = self.evaluator.whnf(constraint) else {
            return false;
        };
        Self::is_data_like(c_val)
            || result_ty == c_val
            || self.is_refinement_of(result_ty, c_val)
            || self.named_constraint_equiv(result_ty, c_val)
    }

    /// Recursively infer the Pi constraint of a term.
    ///
    /// - `Annot(_, ty)` → use the annotation directly.
    /// - `App(f2, a2)` → infer f2's Pi constraint, check a2 against the domain,
    ///   and return the codomain (handles curried applications).
    /// - `Var(i)`     → look up in the context.
    /// - Otherwise    → return `None` (no type information available).
    fn infer_pi_constraint(
        &self,
        ctx: &Context<'bump>,
        f: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        let f_dsg = self.desugar_with_context(f)?;
        match f_dsg {
            Term::Annot(_, ty) => Ok(Some(ty)),
            Term::App(f2, a2) => {
                let Some(f2_ty) = self.infer_pi_constraint(ctx, f2)? else {
                    return Ok(None);
                };
                let ty_norm = self.evaluator.whnf(f2_ty)?;
                match ty_norm {
                    Term::Pi(_, a_dom, b_cod) => {
                        self.check(ctx, a2, a_dom)?;
                        let sub = crate::core::debruijn::SubstitutionContext::new(self.arena);
                        let resolved = sub.instantiate_pi(a2, b_cod);
                        Ok(Some(resolved))
                    }
                    _ => Ok(None),
                }
            }
            _ => {
                let f_val = self.evaluator.whnf(f_dsg)?;
                match f_val {
                    Term::Var(i) => Ok(ctx.lookup(*i)),
                    Term::Builtin(name) | Term::Global(name) => Ok(self.lookup_extern(name)),
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
    ) -> Result<(), Diagnostic> {
        let expected = ctx
            .lookup(i)
            .ok_or_else(|| diag!("unbound term index {}", i))?;
        let expected_val = self.evaluator.whnf(Self::implicit_inner(expected))?;
        let constraint_val = self.evaluator.whnf(Self::implicit_inner(constraint))?;
        if expected_val == constraint_val
            || self.is_refinement_of(expected_val, constraint_val)
            || Self::effect_inner(expected_val).is_some_and(|inner| {
                inner == constraint_val
                    || self.is_refinement_of(inner, constraint_val)
                    || self.named_constraint_equiv(inner, constraint_val)
            })
        {
            Ok(())
        } else {
            Err(diag!(
                "constraint mismatch: declared {}, required {}",
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
    ) -> Result<(), Diagnostic> {
        let bool_name = self.arena.alloc_str(BUILTIN_BOOL);
        self.check(ctx, cond, self.arena.builtin(bool_name))?;
        let ctx_t = add_theorem("_", cond, ctx);
        let ctx_f = add_theorem("_", self.not_term(cond), ctx);
        self.check(&ctx_t, tbranch, constraint)?;
        self.check(&ctx_f, fbranch, constraint)
    }

    /// Check a match expression: use the scrutinee union constraint, then check each branch.
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
        let union_name = match self.evaluator.whnf(scrutinee)? {
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
        let Some(name) = union_name else {
            return Ok(None);
        };
        Ok(self.lookup_union(name).and_then(|(udef, _)| match udef {
            Term::UnionDef(_, variants) => {
                let fields: Vec<_> = variants.iter().map(|(_, f)| *f).collect();
                Some(self.arena.alloc_slice(&fields))
            }
            _ => None,
        }))
    }

    pub(crate) fn check_let(
        &self,
        ctx: &Context<'bump>,
        val: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        mconstr: Option<&'bump Term<'bump>>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let binding_constraint = if let Some(c) = mconstr {
            if Self::is_effect_data_marker(c) {
                let inferred = self.infer_binding_constraint(ctx, val)?;
                let effect_constraint = self.evaluator.whnf(inferred)?;
                if Self::effect_inner(effect_constraint).is_none() {
                    return Err(diag!(
                        "`<-` right-hand side must have an effect constraint, got {}",
                        PrettyPrinter::pretty(effect_constraint)
                    ));
                }
                self.check(ctx, val, effect_constraint)?;
                effect_constraint
            } else {
                self.check(ctx, val, c)?;
                c
            }
        } else {
            let inferred = self.infer_binding_constraint(ctx, val)?;
            self.check(ctx, val, inferred)?;
            inferred
        };
        let new_ctx = extend_ctx_term(binding_constraint, ctx);
        self.check(&new_ctx, body, constraint)
    }

    pub(crate) fn infer_binding_constraint(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let desugared = self.desugar_with_context(term)?;
        match desugared {
            Term::Annot(_, constraint) => Ok(constraint),
            Term::LitInt(_) => Ok(self.arena.builtin(self.arena.alloc_str("int"))),
            Term::LitBool(_) => Ok(self.arena.builtin(self.arena.alloc_str(BUILTIN_BOOL))),
            Term::LitStr(_) => Ok(self.arena.builtin(self.arena.alloc_str("str"))),
            Term::StructCons(sname, _) | Term::Variant(sname, _, _) => {
                Ok(self.arena.builtin(sname))
            }
            Term::Unsafe(inner) => {
                let mut checker = self.clone_for_unsafe();
                checker.unsafe_depth += 1;
                checker.infer_binding_constraint(ctx, inner)
            }
            Term::Pure(inner) => self.infer_pure_constraint(ctx, inner),
            Term::Builtin(name) | Term::Global(name) if self.lookup_extern(name).is_some() => self
                .lookup_extern(name)
                .ok_or_else(|| diag!("missing external function signature: {}", name)),
            Term::StructProj(subject, idx) => {
                self.infer_struct_projection_constraint(ctx, subject, *idx)
            }
            Term::App(f, a) => {
                if let Some(target) = self.ptr_cast_target(f)? {
                    self.infer_ptr_cast_constraint(ctx, target, a)
                } else {
                    self.infer_app_constraint(ctx, f)
                }
            }
            Term::Builtin(name) | Term::Global(name) if self.is_struct_projector_name(name) => {
                Err(diag!("unknown struct field projector: {}", name))
            }
            Term::IfThenElse(_, tbranch, _) | Term::Match(_, [.., (_, _, tbranch)]) => {
                self.infer_binding_constraint(ctx, tbranch)
            }
            Term::Var(i) => ctx
                .lookup(*i)
                .ok_or_else(|| diag!("unbound term index {}", i)),
            _ => Ok(self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA))),
        }
    }

    fn infer_app_constraint(
        &self,
        ctx: &Context<'bump>,
        f: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let f_dsg = self.desugar_with_context(f)?;
        match f_dsg {
            Term::App(inner, _) if matches!(inner, Term::PrimOp(_)) => match inner {
                Term::PrimOp(PrimOp::Add) => {
                    if let Term::App(_, first) = f_dsg {
                        let str_ty = self.arena.builtin(self.arena.alloc_str("str"));
                        if self.check(ctx, first, str_ty).is_ok() {
                            return Ok(str_ty);
                        }
                    }
                    Ok(self.arena.builtin(self.arena.alloc_str("int")))
                }
                Term::PrimOp(PrimOp::Sub | PrimOp::Mul | PrimOp::Div | PrimOp::Mod_) => {
                    Ok(self.arena.builtin(self.arena.alloc_str("int")))
                }
                Term::PrimOp(
                    PrimOp::Eq | PrimOp::Lt | PrimOp::Gt | PrimOp::Le | PrimOp::Ge | PrimOp::Neq,
                ) => Ok(self.arena.builtin(self.arena.alloc_str(BUILTIN_BOOL))),
                _ => unreachable!(),
            },
            Term::PrimOp(op) => match op {
                PrimOp::Add | PrimOp::Sub | PrimOp::Mul | PrimOp::Div | PrimOp::Mod_ => {
                    Ok(self.arena.builtin(self.arena.alloc_str("int")))
                }
                PrimOp::Eq | PrimOp::Lt | PrimOp::Gt | PrimOp::Le | PrimOp::Ge | PrimOp::Neq => {
                    Ok(self.arena.builtin(self.arena.alloc_str(BUILTIN_BOOL)))
                }
            },
            Term::Builtin(name) | Term::Global(name) if self.is_struct_projector_name(name) => {
                Err(diag!("unknown struct field projector: {}", name))
            }
            Term::Builtin(name) | Term::Global(name) if self.lookup_extern(name).is_some() => self
                .lookup_extern(name)
                .ok_or_else(|| diag!("missing external function signature: {}", name)),
            _ => match self.infer_pi_constraint(ctx, f)? {
                Some(ty) => match self.evaluator.whnf(ty)? {
                    Term::Pi(_, _, codomain) => Ok(codomain),
                    other => Err(diag!(
                        "term is not constrained by a Pi term: {}",
                        PrettyPrinter::pretty(other)
                    )),
                },
                None => Ok(self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA))),
            },
        }
    }

    fn ptr_cast_target(
        &self,
        f: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        let f_dsg = self.desugar_with_context(f)?;
        if let Term::App(head, target) = f_dsg
            && matches!(head, Term::Builtin(name) | Term::Global(name) if *name == BUILTIN_PTR_CAST)
        {
            Ok(Some(target))
        } else {
            Ok(None)
        }
    }

    fn ptr_constraint(&self, inner: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena
            .app(self.arena.builtin(self.arena.alloc_str(BUILTIN_PTR)), inner)
    }

    fn check_ptr_cast(
        &self,
        ctx: &Context<'bump>,
        target: &'bump Term<'bump>,
        pointer: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if self.unsafe_depth == 0 {
            return Err(diag!(
                "`{BUILTIN_PTR_CAST}` can only appear in an unsafe context"
            ));
        }
        let result = self.infer_ptr_cast_constraint(ctx, target, pointer)?;
        self.check_domain_match(result, constraint)
    }

    fn infer_ptr_cast_constraint(
        &self,
        ctx: &Context<'bump>,
        target: &'bump Term<'bump>,
        pointer: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let inferred = self.infer_binding_constraint(ctx, pointer)?;
        let inferred_nf = self.evaluator.whnf(inferred)?;
        match inferred_nf {
            Term::App(head, _) if matches!(head, Term::Builtin(name) | Term::Global(name) if *name == BUILTIN_PTR) =>
            {
                self.check(ctx, pointer, inferred)?;
                Ok(self.ptr_constraint(target))
            }
            other => Err(diag!(
                "`{BUILTIN_PTR_CAST}` expects a pointer argument, got {}",
                PrettyPrinter::pretty(other)
            )),
        }
    }

    fn infer_pure_constraint(
        &self,
        ctx: &Context<'bump>,
        inner: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        if self.unsafe_depth == 0 {
            return Err(diag!("`pure` can only appear in an unsafe context"));
        }
        let inferred = self.infer_binding_constraint(ctx, inner)?;
        let effect_constraint = self.evaluator.whnf(inferred)?;
        self.io_inner(effect_constraint).ok_or_else(|| {
            diag!(
                "`pure` expects an IO constraint, got {}",
                PrettyPrinter::pretty(effect_constraint)
            )
        })
    }

    fn infer_struct_projection_constraint(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        idx: usize,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let subject_val = self.evaluator.whnf(subject)?;
        if let Term::StructCons(sname, _) = subject_val {
            return self
                .lookup_struct(sname)
                .and_then(|(sdef, _)| match sdef {
                    Term::StructDef(_, fields) => fields.get(idx).map(|(_, c)| *c),
                    _ => None,
                })
                .ok_or_else(|| diag!("struct {}: no field at index {}", sname, idx));
        }
        if let Term::Var(i) = subject_val {
            let Some(ty) = ctx.lookup(*i) else {
                return Err(Diagnostic::new("term has no known struct constraint"));
            };
            let ty_nf = self.evaluator.whnf(ty)?;
            if let Term::Builtin(sname) | Term::Global(sname) = ty_nf
                && let Some((Term::StructDef(_, fields), _)) = self.lookup_struct(sname)
                && let Some((_, constraint)) = fields.get(idx)
            {
                return Ok(constraint);
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
        match norm {
            Term::Builtin(name) | Term::Global(name) => {
                // Check if term is a Variant — verify union name matches constraint
                if let Term::Variant(uname, _, _) = term
                    && uname == name
                {
                    return Ok(());
                }
                if let Some(builtin_checker) = self.builtins.checker(name) {
                    let evald = self.evaluator.whnf(term)?;
                    builtin_checker(evald)
                } else if let Some((parent, pred)) = lookup_refine(name, &self.table) {
                    self.check(ctx, term, parent)?;
                    self.prove_auto(ctx, term, pred)
                } else if self.lookup_union(name).is_some() {
                    self.check_union_constraint(term, name)
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
                // A Var as a constraint means we have a generic/dependent constraint.
                // Look it up in
                // the context to find the actual constraint.
                if let Some(c) = ctx.lookup(*j) {
                    self.check(ctx, term, c)
                } else {
                    Err(diag!("unbound constraint param at index {}", *j))
                }
            }
            Term::App(head, a) => {
                if matches!(head, Term::Builtin(name) | Term::Global(name) if *name == BUILTIN_IO) {
                    self.check(ctx, term, a)
                } else if matches!(head, Term::Builtin(name) | Term::Global(name) if *name == BUILTIN_PTR)
                {
                    let inferred = self.infer_binding_constraint(ctx, term)?;
                    self.check_domain_match(inferred, norm)
                } else {
                    self.try_check_logical_op(ctx, term, head, a, norm)
                }
            }
            // When a generic union/struct application is resolved via the env,
            // the constraint normalizes to the raw UnionDef/StructDef term.
            Term::UnionDef(uname, _) => self.check_union_constraint(term, uname),
            Term::StructDef(sname, _) => self.check_struct_constraint(term, sname),
            _ => {
                if let Some(result) = self.try_bool_constraint(term, norm) {
                    return result;
                }

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
    }

    fn check_union_constraint(
        &self,
        term: &'bump Term<'bump>,
        expected: &str,
    ) -> Result<(), Diagnostic> {
        if let Term::Variant(actual, _, _) = term {
            if *actual == expected {
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

    fn check_struct_constraint(
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

    pub(crate) fn try_check_logical_op(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        head: &'bump Term<'bump>,
        arg: &'bump Term<'bump>,
        norm: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        // Single-arg case: (not A) — vacuous operators always succeed.
        if let Term::Builtin(name) | Term::Global(name) = head {
            if self.builtins.logic_kind(name) == Some(LogicKind::Vacuous) {
                return Ok(());
            }
            // Check if this is a union/struct constraint application like `Option int`
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
                // Check if this is a multi-arg union/struct constraint application
                if let Some(result) = self.try_check_named_constraint_app(ctx, term, name, norm) {
                    return result;
                }
                self.check_app_constraint(ctx, term, norm)
            }
        }
    }

    /// Check a term against a named constraint application like `Option int` or `Pair int bool`.
    /// Returns `Some(result)` if `name` is a union or struct, `None` otherwise.
    fn try_check_named_constraint_app(
        &self,
        _ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        name: &str,
        _norm: &'bump Term<'bump>,
    ) -> Option<Result<(), Diagnostic>> {
        if self.lookup_union(name).is_some() {
            Some(self.check_union_constraint(term, name))
        } else if self.lookup_struct(name).is_some() {
            Some(self.check_struct_constraint(term, name))
        } else {
            None
        }
    }

    /// Returns true if a field constraint is a generic parameter of the given union.
    fn is_union_generic_param(&self, union_name: &str, constraint: &Term<'bump>) -> bool {
        if let Some((_, type_params)) = self.lookup_union(union_name) {
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

    /// Returns true if a field constraint is a generic parameter of the given struct.
    fn is_struct_generic_param(&self, struct_name: &str, constraint: &Term<'bump>) -> bool {
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

    /// Try to satisfy a constraint by treating it as a boolean predicate.
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

        // Try to treat the constraint as a boolean predicate.
        if let Some(result) = self.try_bool_constraint(term, constraint) {
            return result;
        }

        Err(diag!(
            "cannot use {} as a constraint",
            PrettyPrinter::pretty(constraint)
        ))
    }

    /// Compare two Pi constraints structurally (ignoring parameter names).
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
                if n1 == n2 =>
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

    /// Compare two domain constraints; contravariant: if the declared
    /// domain is `data`, any argument term is accepted.
    pub(crate) fn check_domain_match(
        &self,
        annot: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let a_val = self.evaluator.whnf(Self::implicit_inner(annot))?;
        let c_val = self.evaluator.whnf(Self::implicit_inner(constraint))?;
        // Compare Pi constraints ignoring parameter names (e.g. `Pi("x",A,B)` ≡ `Pi("",A,B)`)
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

    pub(crate) fn constraint_equiv(&self, a: &'bump Term<'bump>, b: &'bump Term<'bump>) -> bool {
        let Ok(a_val) = self.evaluator.whnf(Self::implicit_inner(a)) else {
            return false;
        };
        let Ok(b_val) = self.evaluator.whnf(Self::implicit_inner(b)) else {
            return false;
        };
        a_val == b_val
            || Self::pi_equiv(a_val, b_val)
            || self.named_constraint_equiv(a_val, b_val)
            || self.named_app_equiv(a_val, b_val)
    }

    /// Check if two terms represent the same union/struct constraint application,
    /// even if one side is a resolved `UnionDef`/`StructDef` and the other is
    /// an unresolved `App(Builtin(name), …)`.
    fn named_constraint_equiv(&self, a: &'bump Term<'bump>, b: &'bump Term<'bump>) -> bool {
        let extract = |t: &'bump Term<'bump>| -> Option<&str> {
            match t {
                Term::UnionDef(name, _) | Term::StructDef(name, _) => Some(name),
                Term::App(head, _) => {
                    if let Term::Builtin(n) | Term::Global(n) = *head
                        && (self.lookup_union(n).is_some() || self.lookup_struct(n).is_some())
                    {
                        Some(n)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        };
        match (extract(a), extract(b)) {
            (Some(n1), Some(n2)) => n1 == n2,
            _ => false,
        }
    }

    fn named_app_equiv(&self, a: &'bump Term<'bump>, b: &'bump Term<'bump>) -> bool {
        fn collect<'a>(t: &'a Term<'a>, out: &mut Vec<&'a Term<'a>>) -> &'a Term<'a> {
            match t {
                Term::App(f, arg) => {
                    let head = collect(f, out);
                    out.push(arg);
                    head
                }
                _ => t,
            }
        }
        let mut aa = Vec::new();
        let mut bb = Vec::new();
        let ah = collect(a, &mut aa);
        let bh = collect(b, &mut bb);
        matches!((ah, bh), (Term::Builtin(x) | Term::Global(x), Term::Builtin(y) | Term::Global(y)) if x == y)
            && aa.len() == bb.len()
            && aa
                .iter()
                .zip(bb.iter())
                .all(|(x, y)| self.constraint_equiv(x, y))
    }

    fn is_implicit_meta_constraint(&self, term: &'bump Term<'bump>) -> bool {
        let Ok(inner) = self.evaluator.whnf(Self::implicit_inner(term)) else {
            return false;
        };
        matches!(
            inner,
            Term::Builtin(name) | Term::Global(name)
                if matches!(*name, "prop" | "theorem" | "proof" | "data")
        ) || matches!(
            inner,
            Term::Universe(
                Universe::UProp | Universe::UTheorem | Universe::UProof | Universe::UData
            )
        )
    }

    fn effect_inner(t: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        match t {
            Term::App(_, inner) => Some(inner),
            _ => None,
        }
    }

    fn is_effect_data_marker(t: &'bump Term<'bump>) -> bool {
        if let Term::App(head, inner) = t
            && matches!(head, Term::Builtin(name) | Term::Global(name) if *name == BUILTIN_IO)
        {
            return Self::is_data_like(inner);
        }
        false
    }

    /// Check if two Pi constraints are equivalent ignoring parameter names.
    fn pi_equiv(a: &'bump Term<'bump>, b: &'bump Term<'bump>) -> bool {
        match (a, b) {
            (Term::Pi(_, a_dom, a_cod), Term::Pi(_, b_dom, b_cod)) => {
                a_dom == b_dom && (a_cod == b_cod || Self::pi_equiv(a_cod, b_cod))
            }
            _ => false,
        }
    }

    pub(crate) fn constraint_name<'a>(&self, t: &Term<'a>) -> &'a str {
        match t {
            Term::Builtin(n) | Term::Global(n) => n,
            Term::Refine(n, _, _) => n,
            _ => "?",
        }
    }

    pub(crate) fn is_refinement_of(&self, t1: &'bump Term<'bump>, t2: &'bump Term<'bump>) -> bool {
        if t1 == t2 {
            return true;
        }
        // `data` is the universal constraint — every term is compatible with it.
        if Self::is_data_like(t2) {
            return true;
        }
        match t1 {
            Term::Refine(_, parent, _) => self.is_refinement_of(parent, t2),
            Term::Builtin(n) | Term::Global(n) => lookup_refine(n, &self.table)
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
    ) -> Result<(), Diagnostic> {
        // Look up the struct definition
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
                *fconstraint
            };
            if type_args.is_none() && self.is_generic_param(type_params, fconstraint) {
                continue;
            }
            self.check(ctx, field_values[i], fconstraint).map_err(|e| {
                Diagnostic::new(format!("struct {} field '{}': {}", sname, fname, e))
            })?;
        }
        // Now check the constructed struct against the target constraint
        self.check_by_constraint(ctx, self.arena.struct_cons(sname, field_values), constraint)
    }

    /// Check a union variant construction against a constraint.
    pub(crate) fn check_variant(
        &self,
        ctx: &Context<'bump>,
        uname: Name<'bump>,
        idx: usize,
        payloads: &'bump [&'bump Term<'bump>],
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let (udef, type_params) = self
            .lookup_union(uname)
            .ok_or_else(|| diag!("unknown union: {}", uname))?;
        let Term::UnionDef(_, variants) = udef else {
            return Err(diag!("{} is not a union", uname));
        };
        let (vname, fields) = variants
            .get(idx)
            .ok_or_else(|| diag!("union {}: no variant at index {}", uname, idx))?;
        if payloads.len() != fields.len() {
            return Err(diag!(
                "variant {} expects {} field(s), got {}",
                vname,
                fields.len(),
                payloads.len()
            ));
        }
        for (i, (fname, fconstraint)) in fields.iter().enumerate() {
            if self.is_generic_param(type_params, fconstraint) {
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

    fn constraint_type_args_for(
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
            _ => None,
        }
    }

    fn replace_generic_constraint_vars(
        &self,
        term: &'bump Term<'bump>,
        type_args: &[&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        match term {
            Term::Var(i) if *i < type_args.len() => type_args[type_args.len() - 1 - *i],
            Term::App(f, a) => self.arena.app(
                self.replace_generic_constraint_vars(f, type_args),
                self.replace_generic_constraint_vars(a, type_args),
            ),
            Term::Implicit(inner) => self
                .arena
                .implicit(self.replace_generic_constraint_vars(inner, type_args)),
            Term::Pi(name, a, b) => self.arena.pi(
                name,
                self.replace_generic_constraint_vars(a, type_args),
                self.replace_generic_constraint_vars(b, type_args),
            ),
            Term::Annot(inner, c) => self.arena.annot(
                self.replace_generic_constraint_vars(inner, type_args),
                self.replace_generic_constraint_vars(c, type_args),
            ),
            _ => term,
        }
    }

    /// Check a struct field projection against a constraint.
    pub(crate) fn check_struct_proj(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        idx: usize,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        // First try to evaluate the subject to see if it's a StructCons.
        let subject_val = self.evaluator.whnf(subject)?;
        if let Term::StructCons(sname, field_values) = subject_val {
            // Subject is a concrete struct — get the field value
            if let Some(field_val) = field_values.get(idx) {
                return self.check(ctx, field_val, constraint);
            } else {
                return Err(diag!("struct {}: no field at index {}", sname, idx));
            }
        }
        // For variables, look up the constraint in the context
        if let Term::Var(i) = subject_val {
            if let Some(ty) = ctx.lookup(*i) {
                let ty_nf = self.evaluator.whnf(ty)?;
                if let Term::Builtin(sname) | Term::Global(sname) = ty_nf
                    && let Some((sdef, _)) = self.lookup_struct(sname)
                    && let Term::StructDef(_, fields) = sdef
                    && let Some((_, field_constraint)) = fields.get(idx)
                {
                    // The projection constraint is the field's constraint
                    return self.check_domain_match(field_constraint, constraint);
                }
            }
            return Err(Diagnostic::new("term has no known struct constraint"));
        }
        // Subject is a literal — reject
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
