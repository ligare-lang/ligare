//! De Bruijn index operations: substitution, shifting, and desugaring.

mod destruct;
mod desugar;
mod subst;

pub use destruct::build_destruct_projections;
pub use desugar::{Desugarer, VariantLookup, desugar};
pub use subst::SubstitutionContext;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::pool::TermArena;
    use crate::core::syntax::Term;
    use bumpalo::Bump;

    fn a() -> (&'static Bump, &'static TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        let arena = Box::leak(Box::new(TermArena::new(b)));
        (b, arena)
    }

    fn sub() -> (
        &'static Bump,
        &'static TermArena<'static>,
        SubstitutionContext<'static>,
    ) {
        let (b, arena) = a();
        (b, arena, SubstitutionContext::new(arena))
    }

    #[test]
    fn shift_var_below_cutoff_unchanged() {
        let (_, arena, ctx) = sub();
        let t = ctx.shift(3, 1, arena.var(0));
        assert_eq!(*t, Term::Var(0));
    }

    #[test]
    fn shift_var_above_cutoff_adds_d() {
        let (_, arena, ctx) = sub();
        let t = ctx.shift(2, 0, arena.var(1));
        assert_eq!(*t, Term::Var(3));
    }

    #[test]
    fn shift_under_lam_bumps_cutoff() {
        let (_, arena, ctx) = sub();
        let lam = arena.lam(arena.var(0));
        let t = ctx.shift(1, 0, lam);
        assert_eq!(*t, *arena.lam(arena.var(0)));
    }

    #[test]
    fn shift_under_lam_bumps_var_1_to_2() {
        let (_, arena, ctx) = sub();
        let lam = arena.lam(arena.var(1));
        let t = ctx.shift(1, 0, lam);
        assert_eq!(*t, *arena.lam(arena.var(2)));
    }

    #[test]
    fn subst_replaces_var() {
        let (_, arena, ctx) = sub();
        let t = ctx.subst(arena.lit_int(42), 0, arena.var(0));
        assert_eq!(*t, Term::LitInt(42));
    }

    #[test]
    fn subst_does_not_replace_other_var() {
        let (_, arena, ctx) = sub();
        let t = ctx.subst(arena.lit_int(42), 0, arena.var(1));
        assert_eq!(*t, Term::Var(1));
    }

    #[test]
    fn beta_simple() {
        let (_, arena, ctx) = sub();
        let t = ctx.beta(arena.var(0), arena.lit_int(42));
        assert_eq!(*t, Term::LitInt(42));
    }

    #[test]
    fn beta_preserves_free_vars() {
        let (_, arena, ctx) = sub();
        let t = ctx.beta(arena.var(1), arena.lit_int(42));
        assert_eq!(*t, Term::Var(0));
    }

    #[test]
    fn instantiate_pi_replaces_var_0() {
        let (_, arena, ctx) = sub();
        let t = ctx.instantiate_pi(arena.lit_int(42), arena.var(0));
        assert_eq!(*t, Term::LitInt(42));
    }

    #[test]
    fn instantiate_pi_shifts_free_vars() {
        let (_, arena, ctx) = sub();
        let t = ctx.instantiate_pi(arena.lit_int(42), arena.var(1));
        assert_eq!(*t, Term::Var(0));
    }

    #[test]
    fn desugar_named_to_var() {
        let (_b, arena) = a();
        let desugarer = Desugarer::new(arena);
        let name = arena.alloc_str("x");
        let t = arena.named_lam(name, arena.named(name));
        let d = desugarer.desugar(t);
        assert_eq!(*d, *arena.lam(arena.var(0)));
    }

    #[test]
    fn desugar_nested_named() {
        let (_b, arena) = a();
        let desugarer = Desugarer::new(arena);
        let x = arena.alloc_str("x");
        let y = arena.alloc_str("y");
        let t = arena.named_lam(x, arena.named_lam(y, arena.named(x)));
        let d = desugarer.desugar(t);
        assert_eq!(*d, *arena.lam(arena.lam(arena.var(1))));
    }
}
