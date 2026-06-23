//! Term erasure — removes proof-irrelevant terms.
//!
//! After type-checking, all terms classified as `prop`, `theorem`, or
//! `proof` are erased, leaving only `data` terms for code generation.

use crate::checker::context::Context;
use crate::core::classify::classify;
use crate::core::pool::TermArena;
use crate::core::syntax::{Term, Universe};

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

    /// Erase to plain Term (existing behavior, kept for backward compat).
    pub fn erase(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Let(name, val, body, _mconstr) => {
                let ev = self.erase(val);
                let eb = self.erase(body);
                self.arena.let_(name, ev, eb, None)
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
            | Term::Var(_) => t,
            Term::UnionDef(..) => self.unit(),
            Term::StructDef(..) => self.unit(),
            Term::StructCons(name, field_values) => {
                let ev: Vec<_> = field_values.iter().map(|v| self.erase(v)).collect();
                self.arena.struct_cons(name, self.arena.alloc_slice(&ev))
            }
            Term::StructProj(subject, idx) => self.arena.struct_proj(self.erase(subject), *idx),
            Term::Variant(name, idx, payloads) => {
                let ep: Vec<_> = payloads.iter().map(|p| self.erase(p)).collect();
                self.arena.variant(name, *idx, self.arena.alloc_slice(&ep))
            }
            Term::Match(scrut, branches) => {
                let s = self.erase(scrut);
                let bs: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let eb: Vec<_> = binds.iter().map(|(n, c)| (*n, self.erase(c))).collect();
                        (*idx, self.arena.alloc_slice(&eb), self.erase(body))
                    })
                    .collect();
                self.arena.match_(s, self.arena.alloc_slice(&bs))
            }
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

    fn s<'bump>(arena: &TermArena<'bump>, s: &str) -> &'bump str {
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
