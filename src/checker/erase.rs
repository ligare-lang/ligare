//! Term erasure — removes proof-irrelevant terms.
//!
//! After type-checking, all terms classified as `prop`, `theorem`, or
//! `proof` are erased, leaving only `data` terms for code generation.

use crate::checker::context::Context;
use crate::core::classify::classify;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Term, Universe};

/// Erases proof-irrelevant subterms from a term tree.
pub struct Eraser<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> Eraser<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }

    fn unit(&self) -> &'bump Term<'bump> {
        self.arena.lit_int(0)
    }

    fn is_unit(t: &Term<'_>) -> bool {
        matches!(t, Term::LitInt(0))
    }

    /// Erase to plain Term (existing behavior, kept for backward compat).
    pub fn erase(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Let(name, val, body, _mconstr) => {
                let ev = self.erase(val);
                let eb = self.erase(body);
                self.arena.let_(*name, ev, eb, None)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                let ec = self.erase(cond);
                let et = self.erase(tbranch);
                let ef = self.erase(fbranch);
                self.arena.if_then_else(ec, et, ef)
            }
            Term::Annot(inner, _) => self.erase(inner),
            Term::ByProof(Some(inner), _) => self.erase(inner),
            Term::ByProof(None, _) | Term::AutoProof => self.unit(),
            Term::App(f, a) => {
                if classify(&Context::empty(), f) == Some(Universe::UData) {
                    self.arena.app(self.erase(f), self.erase(a))
                } else {
                    self.unit()
                }
            }
            Term::Func(fname, params, m_ret, body) => {
                let erased_params: Vec<(Name<'bump>, Option<&'bump Term<'bump>>)> = params
                    .iter()
                    .map(|(n, mc)| {
                        let ec = mc.map(|c| self.erase(c));
                        (*n, ec.filter(|c| !Self::is_unit(c)))
                    })
                    .collect();
                let erased_ret = m_ret.map(|r| self.erase(r)).filter(|r| !Self::is_unit(r));
                let erased_body = self.erase(body);
                self.arena.func(
                    *fname,
                    self.arena.alloc_slice(&erased_params),
                    erased_ret,
                    erased_body,
                )
            }
            Term::Pi(..) => self.unit(),
            Term::Refine(_, parent, _pred) => parent,
            Term::Universe(Universe::UData) => t,
            Term::Universe(_) => self.unit(),
            Term::Builtin(_) => {
                if classify(&Context::empty(), t) == Some(Universe::UData) {
                    t
                } else {
                    self.unit()
                }
            }
            Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::Lam(_)
            | Term::PrimOp(_)
            | Term::RefParam
            | Term::This
            | Term::Var(_) => t,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bumpalo::Bump;

    fn setup() -> (&'static Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        (b, TermArena::new(b))
    }

    fn s<'bump>(arena: &TermArena<'bump>, s: &str) -> Name<'bump> {
        arena.alloc_str(s)
    }

    #[test]
    fn lit_int_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.lit_int(42));
        assert_eq!(*t, *arena.lit_int(42));
    }

    #[test]
    fn lit_bool_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.lit_bool(true));
        assert_eq!(*t, *arena.lit_bool(true));
    }

    #[test]
    fn lit_str_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.lit_str(s(&arena, "hi")));
        assert_eq!(*t, *arena.lit_str(s(&arena, "hi")));
    }

    #[test]
    fn lam_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.lam(arena.lit_int(1)));
        assert_eq!(*t, *arena.lam(arena.lit_int(1)));
    }

    #[test]
    fn auto_proof_vanishes() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.auto_proof());
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn pi_vanishes() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let pi = arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "int")),
        );
        let t = eraser.erase(pi);
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn annot_erases_constraint() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let annot = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")));
        let t = eraser.erase(annot);
        assert_eq!(*t, *arena.lit_int(5));
    }

    #[test]
    fn let_keeps_binding() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let term = arena.let_(
            s(&arena, "x"),
            arena.lit_int(5),
            arena.var(0),
            Some(arena.builtin(s(&arena, "int"))),
        );
        let t = eraser.erase(term);
        let expected = arena.let_(s(&arena, "x"), arena.lit_int(5), arena.var(0), None);
        assert_eq!(*t, *expected);
    }
}
