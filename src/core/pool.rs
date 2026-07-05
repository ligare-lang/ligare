use bumpalo::Bump;
use std::cell::RefCell;
use std::collections::HashMap;

use crate::core::syntax::{
    DoStmt, MatchBranch, Name, NamedMatchBranch, NamedStructFieldInit, PrimOp, Tactic, Term,
    Universe,
};

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
        let mut f = |t| f(t);
        self.map_mut(t, &mut f)
    }

    /// Bottom-up tree transformation for closures that carry mutable state.
    pub fn map_mut(
        &self,
        t: &'bump Term<'bump>,
        f: &mut impl FnMut(&'bump Term<'bump>) -> Option<&'bump Term<'bump>>,
    ) -> &'bump Term<'bump> {
        if let Some(r) = f(t) {
            return r;
        }
        match t {
            Term::App(fun, arg) => self.app(self.map_mut(fun, f), self.map_mut(arg, f)),
            Term::Implicit(inner) => self.implicit(self.map_mut(inner, f)),
            Term::Lam(body) => self.lam(self.map_mut(body, f)),
            Term::NamedLam(n, body) => self.named_lam(n, self.map_mut(body, f)),
            Term::Pi(n, a, b) => self.pi(n, self.map_mut(a, f), self.map_mut(b, f)),
            Term::Let(n, v, b, mc) => {
                let mc2 = mc.map(|c| self.map_mut(c, f));
                self.let_(n, self.map_mut(v, f), self.map_mut(b, f), mc2)
            }
            Term::IfThenElse(c, th, el) => {
                self.if_then_else(self.map_mut(c, f), self.map_mut(th, f), self.map_mut(el, f))
            }
            Term::Annot(inner, ct) => self.annot(self.map_mut(inner, f), self.map_mut(ct, f)),
            Term::ByProof(inner, tactics) => {
                let inner_mapped = inner.map(|t| self.map_mut(t, f));
                let mapped: Vec<Tactic<'bump>> = tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => Tactic::Exact(self.map_mut(t, f)),
                        Tactic::Apply(t) => Tactic::Apply(self.map_mut(t, f)),
                        Tactic::Intro(_) => *tac,
                        Tactic::Have(n, t) => Tactic::Have(n, self.map_mut(t, f)),
                        Tactic::Custom(n, args) => {
                            let args = args
                                .iter()
                                .map(|arg| self.map_mut(arg, f))
                                .collect::<Vec<_>>();
                            Tactic::Custom(n, self.alloc_slice(&args))
                        }
                    })
                    .collect();
                self.by_proof(inner_mapped, self.alloc_slice(&mapped))
            }
            Term::Refine(n, par, p) => self.refine(n, self.map_mut(par, f), self.map_mut(p, f)),
            Term::EnumDef(name, variants) => {
                let mapped: Vec<_> = variants
                    .iter()
                    .map(|(vname, fields)| {
                        let mf: Vec<_> = fields
                            .iter()
                            .map(|(fnm, fc)| (*fnm, self.map_mut(fc, f)))
                            .collect();
                        (*vname, self.alloc_slice(&mf))
                    })
                    .collect();
                self.enum_def(name, self.alloc_slice(&mapped))
            }
            Term::Variant(name, idx, payloads) => {
                let mapped: Vec<_> = payloads.iter().map(|p| self.map_mut(p, f)).collect();
                self.variant(name, *idx, self.alloc_slice(&mapped))
            }
            Term::Match(scrut, branches) => {
                let s = self.map_mut(scrut, f);
                let mapped: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let mb: Vec<_> = binds
                            .iter()
                            .map(|(n, c)| (*n, self.map_mut(c, f)))
                            .collect();
                        (*idx, self.alloc_slice(&mb), self.map_mut(body, f))
                    })
                    .collect();
                self.match_(s, self.alloc_slice(&mapped))
            }
            Term::NamedMatch(scrut, branches) => {
                let s = self.map_mut(scrut, f);
                let mapped: Vec<_> = branches
                    .iter()
                    .map(|(variant_name, binds, body)| {
                        let mb: Vec<_> = binds
                            .iter()
                            .map(|(n, c)| (*n, self.map_mut(c, f)))
                            .collect();
                        (*variant_name, self.alloc_slice(&mb), self.map_mut(body, f))
                    })
                    .collect();
                self.named_match(s, self.alloc_slice(&mapped))
            }
            Term::Do(stmts) => {
                let mapped: Vec<_> = stmts
                    .iter()
                    .map(|stmt| match stmt {
                        DoStmt::Bind(n, rhs) => DoStmt::Bind(n, self.map_mut(rhs, f)),
                        DoStmt::Let(n, rhs, mc) => {
                            DoStmt::Let(n, self.map_mut(rhs, f), mc.map(|c| self.map_mut(c, f)))
                        }
                        DoStmt::Expr(expr) => DoStmt::Expr(self.map_mut(expr, f)),
                    })
                    .collect();
                self.do_(self.alloc_slice(&mapped))
            }
            Term::Unsafe(inner) => self.unsafe_(self.map_mut(inner, f)),
            Term::Pure(inner) => self.pure(self.map_mut(inner, f)),
            Term::StructDef(name, fields) => {
                let mf: Vec<_> = fields
                    .iter()
                    .map(|(fnm, fc)| (*fnm, self.map_mut(fc, f)))
                    .collect();
                self.struct_def(name, self.alloc_slice(&mf))
            }
            Term::StructCons(name, field_values) => {
                let mapped: Vec<_> = field_values.iter().map(|v| self.map_mut(v, f)).collect();
                self.struct_cons(name, self.alloc_slice(&mapped))
            }
            Term::NamedStructCons(name, fields) => {
                let mapped: Vec<_> = fields
                    .iter()
                    .map(|(field, value)| (*field, self.map_mut(value, f)))
                    .collect();
                self.named_struct_cons(*name, self.alloc_slice(&mapped))
            }
            Term::StructProj(subject, idx) => self.struct_proj(self.map_mut(subject, f), *idx),
            Term::MethodCall(receiver, method) => {
                self.method_call(self.map_mut(receiver, f), method)
            }
            Term::Quote(inner) => self.quote(self.map_mut(inner, f)),
            Term::Splice(inner) => self.splice(self.map_mut(inner, f)),
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

    pub fn lit_str(&self, s: Name<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::LitStr(s))
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

    pub fn named(&self, name: Name<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Named(name))
    }

    pub fn global(&self, name: Name<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Global(name))
    }

    pub fn auto_proof(&self) -> &'bump Term<'bump> {
        self.alloc(Term::AutoProof)
    }

    pub fn ref_param(&self) -> &'bump Term<'bump> {
        self.alloc(Term::RefParam)
    }

    // ── recursive constructors ──

    pub fn app(&self, f: &'bump Term<'bump>, a: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::App(f, a))
    }

    pub fn implicit(&self, c: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Implicit(c))
    }

    pub fn lam(&self, body: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Lam(body))
    }

    pub fn named_lam(&self, name: Name<'bump>, body: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::NamedLam(name, body))
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

    /// Mechanically expand `intro*; exact t` tactics to a lambda term.
    /// This is used for standalone `by` blocks at runtime.
    pub(crate) fn expand_proof_tactics(
        &self,
        tactics: &'bump [Tactic<'bump>],
    ) -> Result<&'bump Term<'bump>, String> {
        let mut intro_count = 0usize;
        let n = tactics.len();
        for (i, tactic) in tactics.iter().enumerate() {
            let is_last = i == n - 1;
            match tactic {
                Tactic::Intro(_) if !is_last => intro_count += 1,
                Tactic::Exact(t) if is_last => {
                    let mut result = *t;
                    for _ in 0..intro_count {
                        result = self.lam(result);
                    }
                    return Ok(result);
                }
                Tactic::Exact(_) => {
                    return Err("`exact` must be the last tactic".into());
                }
                Tactic::Custom(name, _) => {
                    return Err(format!(
                        "custom tactic `{name}` reached proof eval before metaprogram expansion"
                    ));
                }
                _ => {
                    return Err(
                        "Only `intro`+`exact` tactics are supported in standalone proof eval"
                            .into(),
                    );
                }
            }
        }
        Err("Proof block must end with `exact`".into())
    }

    pub fn enum_def(
        &self,
        name: Name<'bump>,
        variants: &'bump [(Name<'bump>, &'bump [(Name<'bump>, &'bump Term<'bump>)])],
    ) -> &'bump Term<'bump> {
        self.alloc(Term::EnumDef(name, variants))
    }

    pub fn variant(
        &self,
        enum_name: Name<'bump>,
        variant_idx: usize,
        payloads: &'bump [&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Variant(enum_name, variant_idx, payloads))
    }

    pub fn match_(
        &self,
        scrutinee: &'bump Term<'bump>,
        branches: &'bump [MatchBranch<'bump>],
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Match(scrutinee, branches))
    }

    pub fn named_match(
        &self,
        scrutinee: &'bump Term<'bump>,
        branches: &'bump [NamedMatchBranch<'bump>],
    ) -> &'bump Term<'bump> {
        self.alloc(Term::NamedMatch(scrutinee, branches))
    }

    pub fn do_(&self, stmts: &'bump [DoStmt<'bump>]) -> &'bump Term<'bump> {
        self.alloc(Term::Do(stmts))
    }

    pub fn unsafe_(&self, inner: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Unsafe(inner))
    }

    pub fn pure(&self, inner: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Pure(inner))
    }

    pub fn struct_def(
        &self,
        name: Name<'bump>,
        fields: &'bump [(Name<'bump>, &'bump Term<'bump>)],
    ) -> &'bump Term<'bump> {
        self.alloc(Term::StructDef(name, fields))
    }

    pub fn struct_cons(
        &self,
        name: Name<'bump>,
        field_values: &'bump [&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        self.alloc(Term::StructCons(name, field_values))
    }

    pub fn named_struct_cons(
        &self,
        name: Option<Name<'bump>>,
        fields: &'bump [NamedStructFieldInit<'bump>],
    ) -> &'bump Term<'bump> {
        self.alloc(Term::NamedStructCons(name, fields))
    }

    pub fn struct_proj(
        &self,
        subject: &'bump Term<'bump>,
        field_index: usize,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::StructProj(subject, field_index))
    }

    pub fn method_call(
        &self,
        receiver: &'bump Term<'bump>,
        method: Name<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::MethodCall(receiver, method))
    }

    pub fn quote(&self, inner: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Quote(inner))
    }

    pub fn splice(&self, inner: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Splice(inner))
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
