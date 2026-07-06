//! Constraint inference and checking subroutines for `TypeChecker`.

use crate::checker::TypeChecker;
use crate::checker::builtin::LogicKind;
use crate::checker::context::{
    Context, add_refine, add_theorem, expand_constraint, extend_ctx, extend_ctx_term, lookup_refine,
};
use crate::config::{
    BUILTIN_BOOL, BUILTIN_DATA, BUILTIN_IO, BUILTIN_PTR, BUILTIN_PTR_CAST, is_builtin_name,
};
use crate::core::semantics::SemanticQueries;
use crate::core::syntax::{MatchBranch, Name, PrimOp, Term, Universe, compute_level};
use crate::diagnostic::Diagnostic;
use crate::pretty::PrettyPrinter;

type VariantPayloadConstraints<'bump> = &'bump [&'bump [(Name<'bump>, &'bump Term<'bump>)]];

macro_rules! diag {
    ($($arg:tt)*) => {
        Diagnostic::new(format!($($arg)*))
    };
}

mod constraints;
mod control;

impl<'bump> TypeChecker<'bump> {
    /// Returns true if the term represents the universal `data` constraint
    /// (either as `Builtin("data")` or `Universe(UData)`).
    pub(crate) fn is_data_like(t: &Term<'_>) -> bool {
        matches!(t, Term::Builtin(n) | Term::Global(n) if is_builtin_name(n, BUILTIN_DATA))
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
                let type_args = self.constraint_type_args_for(uname, constraint);
                let field_constraint = if let Some(type_args) = type_args.as_deref() {
                    self.replace_generic_constraint_vars(field_constraint, type_args)
                } else {
                    field_constraint
                };
                // If the field constraint is a generic parameter of the enum,
                // skip the field check — the overall constraint check below
                // will verify the variant belongs to the right enum.
                if type_args.is_some() || !self.is_enum_generic_param(uname, field_constraint) {
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
                let type_args = self.constraint_type_args_for(sname, constraint);
                let field_constraint = if let Some(type_args) = type_args.as_deref() {
                    self.replace_generic_constraint_vars(field_constraint, type_args)
                } else {
                    field_constraint
                };
                // If the field constraint is a generic parameter of the struct,
                // skip the field check.
                if type_args.is_some() || !self.is_struct_generic_param(sname, field_constraint) {
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
            || self.named_constraint_equiv(expected_val, constraint_val)
            || Self::effect_inner(expected_val).is_some_and(|inner| {
                inner == constraint_val
                    || self.is_refinement_of(inner, constraint_val)
                    || self.named_constraint_equiv(inner, constraint_val)
            })
        {
            self.check_var_universe_level(constraint)
        } else {
            Err(diag!(
                "constraint mismatch: declared {}, required {}",
                PrettyPrinter::pretty(expected_val),
                PrettyPrinter::pretty(constraint_val)
            ))
        }
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

    pub fn infer_binding_constraint(
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
            Term::MethodCall(..) => Err(diag!(
                "method call reached constraint inference before resolution"
            )),
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
            && matches!(head, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_PTR_CAST))
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
            Term::App(Term::Builtin(name) | Term::Global(name), _)
                if is_builtin_name(name, BUILTIN_PTR) =>
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
}
