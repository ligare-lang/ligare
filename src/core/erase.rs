//! Term erasure — removes proof-irrelevant terms.
//!
//! After type-checking, all terms classified as `prop`, `theorem`, or
//! `proof` are erased, leaving only `data` terms for code generation.
//!
//! ## Approach
//!
//! Structural terms (`Let`, `If`, `Annot`, `ByProof`) always recurse
//! into children.  Leaf and semi-leaf terms use universe classification
//! to decide whether to keep or replace with `0` (the unit value).

use crate::checker::context::Context;
use crate::core::classify::classify;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Term, Universe};

/// The unit value used to replace erased terms.
fn unit<'bump>(arena: &'bump TermArena<'bump>) -> &'bump Term<'bump> {
    arena.lit_int(0)
}

/// Check whether a term is the erasure unit value (structural check,
/// not pointer equality).
fn is_unit(t: &Term<'_>) -> bool {
    matches!(t, Term::LitInt(0))
}

/// Erase all non-`data` subterms, returning a term that contains only
/// runtime-relevant `data` computation.
pub fn erase<'bump>(arena: &'bump TermArena<'bump>, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
    match t {
        // ── Structural terms — always recurse into children ──
        Term::Let(name, val, body, _mconstr) => {
            let ev = erase(arena, val);
            let eb = erase(arena, body);
            arena.let_(*name, ev, eb, None)
        }

        Term::IfThenElse(cond, tbranch, fbranch) => {
            let ec = erase(arena, cond);
            let et = erase(arena, tbranch);
            let ef = erase(arena, fbranch);
            arena.if_then_else(ec, et, ef)
        }

        Term::Annot(inner, _) => erase(arena, inner),

        Term::ByProof(Some(inner), _) => erase(arena, inner),
        Term::ByProof(None, _) | Term::AutoProof => unit(arena),

        // ── Application — keep only if the function is data-level ──
        Term::App(f, a) => {
            if classify(&Context::empty(), f) == Some(Universe::UData) {
                arena.app(erase(arena, f), erase(arena, a))
            } else {
                unit(arena)
            }
        }

        // ── Func — erase parameter constraints and return type ──
        Term::Func(fname, params, m_ret, body) => {
            // Erase each constraint; if it becomes unit, drop to None.
            let erased_params: Vec<(Name<'bump>, Option<&'bump Term<'bump>>)> = params
                .iter()
                .map(|(n, mc)| {
                    let ec = mc.map(|c| erase(arena, c));
                    (*n, ec.filter(|c| !is_unit(c)))
                })
                .collect();
            let erased_ret = m_ret.map(|r| erase(arena, r)).filter(|r| !is_unit(r));
            let erased_body = erase(arena, body);
            arena.func(
                *fname,
                arena.alloc_slice(&erased_params),
                erased_ret,
                erased_body,
            )
        }

        // ── Pi / Refine — prop-level, erase ──
        Term::Pi(..) => unit(arena),
        // Refinement: keep the parent type (it's a type name, not
        // runtime data — the C backend filters it out).  Erase the
        // predicate.
        Term::Refine(_, parent, _pred) => parent,

        // ── Universe — keep only UData ──
        Term::Universe(Universe::UData) => t,
        Term::Universe(_) => unit(arena),

        // ── Builtin — keep only data-classified builtins ──
        Term::Builtin(_) => {
            if classify(&Context::empty(), t) == Some(Universe::UData) {
                t
            } else {
                unit(arena)
            }
        }

        // ── Leaves — all data, keep as-is ──
        Term::LitInt(_)
        | Term::LitBool(_)
        | Term::Lam(_)
        | Term::PrimOp(_)
        | Term::RefParam
        | Term::This
        | Term::Var(_) => t,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::syntax::Tactic;
    use bumpalo::Bump;

    fn setup() -> (&'static Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        (b, TermArena::new(b))
    }

    fn s<'bump>(arena: &TermArena<'bump>, s: &str) -> crate::core::syntax::Name<'bump> {
        arena.alloc_str(s)
    }

    // ── Data leaves survive ──

    #[test]
    fn lit_int_survives() {
        let (_b, arena) = setup();
        let t = erase(&arena, arena.lit_int(42));
        assert_eq!(*t, *arena.lit_int(42));
    }

    #[test]
    fn lit_bool_survives() {
        let (_b, arena) = setup();
        let t = erase(&arena, arena.lit_bool(true));
        assert_eq!(*t, *arena.lit_bool(true));
    }

    #[test]
    fn lam_survives() {
        let (_b, arena) = setup();
        let t = erase(&arena, arena.lam(arena.lit_int(1)));
        assert_eq!(*t, *arena.lam(arena.lit_int(1)));
    }

    #[test]
    fn var_survives() {
        let (_b, arena) = setup();
        let t = erase(&arena, arena.var(0));
        assert_eq!(*t, *arena.var(0));
    }

    #[test]
    fn app_of_data_survives() {
        let (_b, arena) = setup();
        let add = arena.prim_op(crate::core::syntax::PrimOp::Add);
        let app = arena.app(arena.app(add, arena.lit_int(1)), arena.lit_int(2));
        let t = erase(&arena, app);
        assert!(!matches!(*t, Term::LitInt(0)));
    }

    // ── Proof / prop leaves vanish ──

    #[test]
    fn auto_proof_vanishes() {
        let (_b, arena) = setup();
        let t = erase(&arena, arena.auto_proof());
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn by_proof_none_vanishes() {
        let (_b, arena) = setup();
        let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]);
        let t = erase(&arena, arena.by_proof(None, tactics));
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn by_proof_some_keeps_subject() {
        let (_b, arena) = setup();
        let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]);
        let term = arena.by_proof(Some(arena.lit_int(42)), tactics);
        let t = erase(&arena, term);
        assert_eq!(*t, *arena.lit_int(42));
    }

    #[test]
    fn pi_vanishes() {
        let (_b, arena) = setup();
        let pi = arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "int")),
        );
        let t = erase(&arena, pi);
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn refine_keeps_parent() {
        let (_b, arena) = setup();
        let refine = arena.refine(
            s(&arena, "nat"),
            arena.builtin(s(&arena, "int")),
            arena.lit_bool(true),
        );
        // Parent type is kept as-is (not re-erased — it's a type name).
        let t = erase(&arena, refine);
        assert_eq!(*t, *arena.builtin(s(&arena, "int")));
    }

    #[test]
    fn annot_erases_constraint() {
        let (_b, arena) = setup();
        let annot = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")));
        let t = erase(&arena, annot);
        assert_eq!(*t, *arena.lit_int(5));
    }

    // ── Structural terms ──

    #[test]
    fn let_keeps_binding() {
        let (_b, arena) = setup();
        let term = arena.let_(
            s(&arena, "x"),
            arena.by_proof(
                Some(arena.lit_int(5)),
                arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]),
            ),
            arena.var(0),
            Some(arena.builtin(s(&arena, "int"))),
        );
        // After erasure: let x = 5 in x  (proof and constraint gone)
        let t = erase(&arena, term);
        let expected = arena.let_(s(&arena, "x"), arena.lit_int(5), arena.var(0), None);
        assert_eq!(*t, *expected);
    }

    #[test]
    fn if_erases_branches() {
        let (_b, arena) = setup();
        let term = arena.if_then_else(
            arena.lit_bool(true),
            arena.by_proof(
                Some(arena.lit_int(10)),
                arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]),
            ),
            arena.lit_int(20),
        );
        let t = erase(&arena, term);
        let expected =
            arena.if_then_else(arena.lit_bool(true), arena.lit_int(10), arena.lit_int(20));
        assert_eq!(*t, *expected);
    }

    #[test]
    fn func_erases_param_constraints() {
        let (_b, arena) = setup();
        let func = arena.func(
            s(&arena, "f"),
            arena.alloc_slice(&[(s(&arena, "x"), Some(arena.builtin(s(&arena, "int"))))]),
            Some(arena.builtin(s(&arena, "int"))),
            arena.var(0),
        );
        let t = erase(&arena, func);
        // Parameter constraint and return type become None (erased to unit).
        let expected = arena.func(
            s(&arena, "f"),
            arena.alloc_slice(&[(s(&arena, "x"), None)]),
            None,
            arena.var(0),
        );
        assert_eq!(*t, *expected);
    }

    #[test]
    fn builtin_proof_vanishes() {
        let (_b, arena) = setup();
        let t = erase(&arena, arena.builtin(s(&arena, "proof")));
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn builtin_int_vanishes() {
        let (_b, arena) = setup();
        let t = erase(&arena, arena.builtin(s(&arena, "int")));
        // `int` is prop-classified, so it vanishes
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn app_of_logic_vanishes() {
        let (_b, arena) = setup();
        // `∧ true false` — and is prop-classified
        let and_term = arena.app(
            arena.app(arena.builtin(s(&arena, "and")), arena.lit_bool(true)),
            arena.lit_bool(false),
        );
        let t = erase(&arena, and_term);
        assert_eq!(*t, *arena.lit_int(0));
    }
}
