use bumpalo::Bump;
use std::cell::RefCell;
use std::collections::HashMap;

use crate::core::syntax::{Name, PrimOp, Tactic, Term, Universe};

/// A bumpalo-backed string interner.
///
/// Uses a bump arena to allocate strings, ensuring that identical strings
/// share the same allocation (backed by a hash map for O(1) lookup).
///
/// Threaded through `CompState` so the checker and evaluator can
/// use arena-allocated strings to reduce heap fragmentation.
pub struct StringPool<'bump> {
    bump: &'bump Bump,
    /// Intern table: caches previously allocated strings so identical
    /// strings share the same bump-allocated pointer.
    intern: RefCell<HashMap<&'bump str, &'bump str>>,
}

impl<'bump> StringPool<'bump> {
    pub fn new(bump: &'bump Bump) -> Self {
        Self {
            bump,
            intern: RefCell::new(HashMap::new()),
        }
    }

    /// Allocate a `&str` in the bump arena.
    #[inline]
    pub fn alloc_str(&self, s: &str) -> &'bump str {
        self.bump.alloc_str(s)
    }

    /// Intern a string: return a bump-allocated `&str`.
    /// Reuses an existing allocation if the same string was already interned (O(1)).
    pub fn intern(&self, s: &str) -> &'bump str {
        let mut intern = self.intern.borrow_mut();
        if let Some(&existing) = intern.get(s) {
            return existing;
        }
        let allocated: &'bump str = self.bump.alloc_str(s);
        intern.insert(allocated, allocated);
        allocated
    }

    /// Access the underlying bump allocator.
    #[inline]
    pub fn bump(&self) -> &'bump Bump {
        self.bump
    }
}

// ── TermArena: fast bump-allocated Term construction ──

/// A bumpalo arena for constructing `Term` nodes efficiently.
///
/// During checking and evaluation, many intermediate terms are created.
/// This arena avoids individual heap allocations by allocating all
/// temporary nodes in a single bump region.
pub struct TermArena<'bump> {
    bump: &'bump Bump,
}

impl<'bump> TermArena<'bump> {
    pub fn new(bump: &'bump Bump) -> Self {
        Self { bump }
    }

    /// Access the underlying bump allocator.
    #[inline]
    pub fn bump(&self) -> &'bump Bump {
        self.bump
    }

    /// Allocate a `Term` directly into the arena.
    #[inline]
    pub fn alloc(&self, t: Term<'bump>) -> &'bump Term<'bump> {
        self.bump.alloc(t)
    }

    /// Allocate a `&str` into the arena.
    #[inline]
    pub fn alloc_str(&self, s: &str) -> &'bump str {
        self.bump.alloc_str(s)
    }

    /// Allocate a copy of a slice into the arena.
    #[inline]
    pub fn alloc_slice<T: Copy>(&self, data: &[T]) -> &'bump [T] {
        if data.is_empty() {
            &[]
        } else {
            self.bump.alloc_slice_copy(data)
        }
    }

    /// Bottom-up tree transformation.  `f` is called on every node;
    /// returning `Some(t)` replaces the node, `None` recurses into children.
    pub fn map(
        &self,
        t: &'bump Term<'bump>,
        f: &impl Fn(&'bump Term<'bump>) -> Option<&'bump Term<'bump>>,
    ) -> &'bump Term<'bump> {
        if let Some(r) = f(t) {
            return r;
        }
        match t {
            Term::App(fun, arg) => self.app(self.map(fun, f), self.map(arg, f)),
            Term::Lam(body) => self.lam(self.map(body, f)),
            Term::Pi(n, a, b) => self.pi(n, self.map(a, f), self.map(b, f)),
            Term::Let(n, v, b, mc) => {
                let mc2 = mc.map(|c| self.map(c, f));
                self.let_(n, self.map(v, f), self.map(b, f), mc2)
            }
            Term::IfThenElse(c, th, el) => {
                self.if_then_else(self.map(c, f), self.map(th, f), self.map(el, f))
            }
            Term::Annot(inner, ct) => self.annot(self.map(inner, f), self.map(ct, f)),
            Term::ByProof(inner, tactics) => {
                let inner_mapped = inner.map(|t| self.map(t, f));
                let mapped: Vec<Tactic<'bump>> = tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => Tactic::Exact(self.map(t, f)),
                        Tactic::Apply(t) => Tactic::Apply(self.map(t, f)),
                        Tactic::Intro(_) => *tac,
                        Tactic::Have(n, t) => Tactic::Have(n, self.map(t, f)),
                    })
                    .collect();
                self.by_proof(inner_mapped, self.alloc_slice(&mapped))
            }
            Term::Refine(n, par, p) => self.refine(n, self.map(par, f), self.map(p, f)),
            Term::Func(fname, params, m_ret, body) => {
                let params2: Vec<_> = params
                    .iter()
                    .map(|(nm, mc)| (*nm, mc.map(|c| self.map(c, f))))
                    .collect();
                self.func(
                    fname,
                    self.alloc_slice(&params2),
                    m_ret.map(|c| self.map(c, f)),
                    self.map(body, f),
                )
            }
            _ => t,
        }
    }

    // ── leaf constructors ──

    pub fn var(&self, i: usize) -> &'bump Term<'bump> {
        self.alloc(Term::Var(i))
    }

    pub fn lit_int(&self, n: i64) -> &'bump Term<'bump> {
        self.alloc(Term::LitInt(n))
    }

    pub fn lit_bool(&self, b: bool) -> &'bump Term<'bump> {
        self.alloc(Term::LitBool(b))
    }

    pub fn prim_op(&self, op: PrimOp) -> &'bump Term<'bump> {
        self.alloc(Term::PrimOp(op))
    }

    pub fn universe(&self, u: Universe) -> &'bump Term<'bump> {
        self.alloc(Term::Universe(u))
    }

    pub fn builtin(&self, name: Name<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Builtin(name))
    }

    pub fn auto_proof(&self) -> &'bump Term<'bump> {
        self.alloc(Term::AutoProof)
    }

    pub fn ref_param(&self) -> &'bump Term<'bump> {
        self.alloc(Term::RefParam)
    }

    pub fn this_(&self) -> &'bump Term<'bump> {
        self.alloc(Term::This)
    }

    // ── recursive constructors ──

    pub fn app(&self, f: &'bump Term<'bump>, a: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::App(f, a))
    }

    pub fn lam(&self, body: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Lam(body))
    }

    pub fn pi(
        &self,
        name: Name<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Pi(name, a, b))
    }

    pub fn let_(
        &self,
        name: Name<'bump>,
        val: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        mconstr: Option<&'bump Term<'bump>>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Let(name, val, body, mconstr))
    }

    pub fn if_then_else(
        &self,
        cond: &'bump Term<'bump>,
        th: &'bump Term<'bump>,
        el: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::IfThenElse(cond, th, el))
    }

    pub fn refine(
        &self,
        name: Name<'bump>,
        parent: &'bump Term<'bump>,
        pred: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Refine(name, parent, pred))
    }

    pub fn annot(&self, t: &'bump Term<'bump>, c: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Annot(t, c))
    }

    pub fn by_proof(
        &self,
        t: Option<&'bump Term<'bump>>,
        tactics: &'bump [Tactic<'bump>],
    ) -> &'bump Term<'bump> {
        self.alloc(Term::ByProof(t, tactics))
    }

    pub fn func(
        &self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Func(name, params, m_ret, body))
    }
}

// ── SubstitutionContext: encapsulates debruijn operations ──

/// Encapsulates de Bruijn index substitution and shifting operations.
///
/// These operations traverse the term tree and allocate new nodes in the
/// arena as needed.  By bundling the arena reference, callers avoid
/// passing it as a separate argument to every function.
pub struct SubstitutionContext<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> SubstitutionContext<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Substitute: replace de Bruijn index `i` with `s` in term `t`.
    pub fn subst(
        &self,
        s: &'bump Term<'bump>,
        i: usize,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.subst_cutoff(s, i, 0, t)
    }

    fn subst_cutoff(
        &self,
        s: &'bump Term<'bump>,
        i: usize,
        cutoff: usize,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        if let Term::Var(j) = t
            && *j == i + cutoff
        {
            return self.shift(cutoff as i32, 0, s);
        }
        self.traverse_children(t, cutoff as i32, |t, c| {
            self.subst_cutoff(s, i, c as usize, t)
        })
    }

    /// Shift: add `d` to all de Bruijn indices >= `cutoff`.
    pub fn shift(&self, d: i32, cutoff: i32, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Term::Var(j) = t
            && (*j as i32) >= cutoff
        {
            return self.arena.var((*j as i32 + d) as usize);
        }
        self.traverse_children(t, cutoff, |t, c| self.shift(d, c, t))
    }

    /// Shared children-recursion for `shift` and `subst_cutoff`.
    /// For nodes that bind variables (Lam, Pi, Let, Func), `cutoff` is bumped.
    fn traverse_children(
        &self,
        t: &'bump Term<'bump>,
        cutoff: i32,
        recurse: impl Fn(&'bump Term<'bump>, i32) -> &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::Lam(body) => self.arena.lam(recurse(body, cutoff + 1)),
            Term::App(f, a) => self.arena.app(recurse(f, cutoff), recurse(a, cutoff)),
            Term::Pi(n, a, b) => self.arena.pi(n, recurse(a, cutoff), recurse(b, cutoff + 1)),
            Term::Let(n, v, b, mc) => {
                let mc2 = mc.map(|c| recurse(c, cutoff));
                self.arena
                    .let_(n, recurse(v, cutoff), recurse(b, cutoff + 1), mc2)
            }
            Term::IfThenElse(c, th, el) => self.arena.if_then_else(
                recurse(c, cutoff),
                recurse(th, cutoff),
                recurse(el, cutoff),
            ),
            Term::Annot(inner, ct) => self
                .arena
                .annot(recurse(inner, cutoff), recurse(ct, cutoff)),
            Term::ByProof(inner, tactics) => {
                let inner_mapped = inner.map(|t| recurse(t, cutoff));
                let mapped: Vec<Tactic<'bump>> = tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => Tactic::Exact(recurse(t, cutoff)),
                        Tactic::Apply(t) => Tactic::Apply(recurse(t, cutoff)),
                        Tactic::Intro(_) => *tac,
                        Tactic::Have(n, t) => Tactic::Have(n, recurse(t, cutoff)),
                    })
                    .collect();
                self.arena
                    .by_proof(inner_mapped, self.arena.alloc_slice(&mapped))
            }
            Term::Refine(n, par, p) => {
                self.arena
                    .refine(n, recurse(par, cutoff), recurse(p, cutoff))
            }
            Term::Func(fname, params, m_ret, body) => {
                let params2: Vec<_> = params
                    .iter()
                    .map(|(nm, mc)| (*nm, mc.map(|c| recurse(c, cutoff))))
                    .collect();
                self.arena.func(
                    fname,
                    self.arena.alloc_slice(&params2),
                    m_ret.map(|c| recurse(c, cutoff)),
                    recurse(body, cutoff + params.len() as i32),
                )
            }
            // Leaf nodes — returned unchanged (Var handled by callers)
            _ => t,
        }
    }

    /// Beta-reduction: substitute arg into the body of a lambda.
    pub fn beta(
        &self,
        lam_body: &'bump Term<'bump>,
        arg: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let shifted_arg = self.shift(1, 0, arg);
        let substituted = self.subst(shifted_arg, 0, lam_body);
        self.shift(-1, 0, substituted)
    }

    /// Shift that preserves `RefParam` (leaves it untouched).
    pub fn shift_preserve_refparam(&self, d: i32, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.shift_refparam_cutoff(d, 0, t)
    }

    fn shift_refparam_cutoff(
        &self,
        d: i32,
        cutoff: i32,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::RefParam => t,
            Term::Var(i) => {
                if (*i as i32) >= cutoff {
                    self.arena.var((*i as i32 + d) as usize)
                } else {
                    t
                }
            }
            _ => self.shift(d, cutoff, t),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_pool_basic() {
        let bump = Bump::new();
        let pool = StringPool::new(&bump);

        let a = pool.alloc_str("hello");
        let b = pool.alloc_str("hello");
        assert_eq!(a, b);
    }

    #[test]
    fn test_string_pool_intern() {
        let bump = Bump::new();
        let pool = StringPool::new(&bump);

        let a = pool.intern("world");
        let b = pool.intern("world");
        assert_eq!(a, b);
        // Should be the same pointer since it was interned
        assert_eq!(a.as_ptr(), b.as_ptr());
    }
}
