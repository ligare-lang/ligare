use std::fmt;

use crate::config::{UNIVERSE_DATA, UNIVERSE_PROOF, UNIVERSE_PROP, UNIVERSE_THEOREM};
use crate::core::pool::TermArena;

/// A name in the AST, arena-allocated for zero-copy sharing.
pub type Name<'bump> = &'bump str;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Universe {
    UData,
    UProp,
    UTheorem,
    UProof,
}

impl fmt::Display for Universe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Universe::UData => write!(f, "{UNIVERSE_DATA}"),
            Universe::UProp => write!(f, "{UNIVERSE_PROP}"),
            Universe::UTheorem => write!(f, "{UNIVERSE_THEOREM}"),
            Universe::UProof => write!(f, "{UNIVERSE_PROOF}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod_,
    Eq,
    Lt,
    Gt,
    Le,
    Ge,
    Neq,
}

impl fmt::Display for PrimOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimOp::Add => write!(f, "+"),
            PrimOp::Sub => write!(f, "-"),
            PrimOp::Mul => write!(f, "*"),
            PrimOp::Div => write!(f, "/"),
            PrimOp::Mod_ => write!(f, "%"),
            PrimOp::Eq => write!(f, "=="),
            PrimOp::Lt => write!(f, "<"),
            PrimOp::Gt => write!(f, ">"),
            PrimOp::Le => write!(f, "<="),
            PrimOp::Ge => write!(f, ">="),
            PrimOp::Neq => write!(f, "/="),
        }
    }
}

/// The core Term, arena-allocated via bumpalo.
///
/// All recursive positions use `&'bump Term<'bump>` references instead of
/// `Box<Term>`, eliminating per-node heap allocations.  The entire term tree
/// lives in a single bump arena for fast allocation and excellent cache
/// locality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Term<'bump> {
    Var(usize),
    App(&'bump Term<'bump>, &'bump Term<'bump>),
    Lam(&'bump Term<'bump>),
    LitInt(i64),
    LitBool(bool),
    PrimOp(PrimOp),
    Universe(Universe),
    Builtin(Name<'bump>),
    Pi(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Let(
        Name<'bump>,
        &'bump Term<'bump>,
        &'bump Term<'bump>,
        Option<&'bump Term<'bump>>,
    ),
    IfThenElse(&'bump Term<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Refine(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Annot(&'bump Term<'bump>, &'bump Term<'bump>),
    ByProof(&'bump Term<'bump>, &'bump Term<'bump>),
    AutoProof,
    RefParam,
    This,
    Func(
        Name<'bump>,
        &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        Option<&'bump Term<'bump>>,
        &'bump [Term<'bump>],
        &'bump [Term<'bump>],
        &'bump Term<'bump>,
    ),
    ProofBlock(&'bump Term<'bump>),
}

// ── TermVisitor: a trait for polymorphic term traversal ──

/// A visitor that walks over a `Term` tree, allowing custom logic at each node.
///
/// Implementors override the methods for the variants they care about;
/// the default implementations simply recurse into children.
///
/// The `walk` method drives the traversal.  Because Term nodes are arena-allocated
/// and immutable, the visitor returns `Option<&'bump Term<'bump>>` — `Some(new)` to
/// replace the node, or `None` to keep it unchanged.
pub trait TermVisitor<'bump> {
    /// The arena used for allocating replacement nodes.
    fn arena(&self) -> &TermArena<'bump>;

    fn visit_var(&self, _i: usize) -> Option<&'bump Term<'bump>> {
        None
    }
    fn visit_lam(&self, body: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        let b = self.walk(body);
        Some(self.arena().lam(b))
    }
    fn visit_app(
        &self,
        f: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let f2 = self.walk(f);
        let a2 = self.walk(a);
        Some(self.arena().app(f2, a2))
    }
    fn visit_pi(
        &self,
        name: Name<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let a2 = self.walk(a);
        let b2 = self.walk(b);
        Some(self.arena().pi(name, a2, b2))
    }
    fn visit_let(
        &self,
        name: Name<'bump>,
        val: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        mconstr: Option<&'bump Term<'bump>>,
    ) -> Option<&'bump Term<'bump>> {
        let v2 = self.walk(val);
        let mc2 = mconstr.map(|c| self.walk(c));
        let b2 = self.walk(body);
        Some(self.arena().let_(name, v2, b2, mc2))
    }
    fn visit_if(
        &self,
        cond: &'bump Term<'bump>,
        th: &'bump Term<'bump>,
        el: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let c2 = self.walk(cond);
        let th2 = self.walk(th);
        let el2 = self.walk(el);
        Some(self.arena().if_then_else(c2, th2, el2))
    }
    fn visit_annot(
        &self,
        t: &'bump Term<'bump>,
        c: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let t2 = self.walk(t);
        let c2 = self.walk(c);
        Some(self.arena().annot(t2, c2))
    }
    fn visit_by_proof(
        &self,
        t: &'bump Term<'bump>,
        p: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let t2 = self.walk(t);
        let p2 = self.walk(p);
        Some(self.arena().by_proof(t2, p2))
    }
    fn visit_refine(
        &self,
        name: Name<'bump>,
        parent: &'bump Term<'bump>,
        pred: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let par2 = self.walk(parent);
        let p2 = self.walk(pred);
        Some(self.arena().refine(name, par2, p2))
    }
    fn visit_proof_block(&self, inner: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        let i2 = self.walk(inner);
        Some(self.arena().proof_block(i2))
    }

    /// Walk the entire term tree, dispatching to the appropriate visitor method.
    fn walk(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Var(i) => self.visit_var(*i).unwrap_or(t),
            Term::Lam(body) => self.visit_lam(body).unwrap_or(t),
            Term::App(f, a) => self.visit_app(f, a).unwrap_or(t),
            Term::Pi(n, a, b) => self.visit_pi(n, a, b).unwrap_or(t),
            Term::Let(n, v, b, mc) => self.visit_let(n, v, b, *mc).unwrap_or(t),
            Term::IfThenElse(c, th, el) => self.visit_if(c, th, el).unwrap_or(t),
            Term::Annot(inner, ct) => self.visit_annot(inner, ct).unwrap_or(t),
            Term::ByProof(inner, p) => self.visit_by_proof(inner, p).unwrap_or(t),
            Term::Refine(n, par, p) => self.visit_refine(n, par, p).unwrap_or(t),
            Term::ProofBlock(inner) => self.visit_proof_block(inner).unwrap_or(t),
            // Leaf nodes — keep as-is
            _ => t,
        }
    }
}
