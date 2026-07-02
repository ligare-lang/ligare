use std::fmt;

use crate::config::{UNIVERSE_DATA, UNIVERSE_PROOF, UNIVERSE_PROP, UNIVERSE_THEOREM};

pub type Name<'bump> = &'bump str;

/// A match branch: (variant_index, [(bind_name, bind_type)], body).
pub type MatchBranch<'bump> = (
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    &'bump Term<'bump>,
);

/// A parser-level match branch: (variant_name, [(bind_name, fallback_type)], body).
pub type NamedMatchBranch<'bump> = (
    Name<'bump>,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    &'bump Term<'bump>,
);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DoStmt<'bump> {
    Bind(Name<'bump>, &'bump Term<'bump>),
    Let(Name<'bump>, &'bump Term<'bump>, Option<&'bump Term<'bump>>),
    Expr(&'bump Term<'bump>),
}

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

impl<'bump> Term<'bump> {
    /// Returns true if this is a desugared zero-parameter definition
    /// (a constant), i.e. `Annot(body, _)` where body is NOT a `Lam` or `NamedLam`.
    pub fn is_constant(&self) -> bool {
        matches!(self, Term::Annot(body, _) if !matches!(body, Term::Lam(_) | Term::NamedLam(_, _)))
    }
}

impl PrimOp {
    pub fn apply(&self, x: i64, y: i64) -> Term<'static> {
        match self {
            PrimOp::Add => Term::LitInt(x.wrapping_add(y)),
            PrimOp::Sub => Term::LitInt(x.wrapping_sub(y)),
            PrimOp::Mul => Term::LitInt(x.wrapping_mul(y)),
            PrimOp::Div => Term::LitInt(if y == 0 { 0 } else { x / y }),
            PrimOp::Mod_ => Term::LitInt(if y == 0 { 0 } else { x % y }),
            PrimOp::Eq => Term::LitBool(x == y),
            PrimOp::Lt => Term::LitBool(x < y),
            PrimOp::Gt => Term::LitBool(x > y),
            PrimOp::Le => Term::LitBool(x <= y),
            PrimOp::Ge => Term::LitBool(x >= y),
            PrimOp::Neq => Term::LitBool(x != y),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tactic<'bump> {
    /// `exact <term>` — the proof is exactly this term.
    Exact(&'bump Term<'bump>),
    /// `apply <term>` — backward reasoning: if goal is B and term : A -> B,
    /// the new goal becomes A.
    Apply(&'bump Term<'bump>),
    /// `intro` or `intro <name>` — introduce a hypothesis for Pi goals.
    /// Produces a lambda that binds the introduced variable.
    Intro(Option<Name<'bump>>),
    /// `have <name> := <term>` — prove an intermediate lemma, add it to
    /// the context as a theorem, and continue.
    Have(Name<'bump>, &'bump Term<'bump>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Term<'bump> {
    Var(usize),
    App(&'bump Term<'bump>, &'bump Term<'bump>),
    /// Marker for an implicit parameter constraint. This wrapper lives only in
    /// signatures; the wrapped constraint is used for checking and instance lookup.
    Implicit(&'bump Term<'bump>),
    Lam(&'bump Term<'bump>),
    /// Named lambda (parser artifact): stores param name, resolved to Lam+Var by desugar.
    NamedLam(Name<'bump>, &'bump Term<'bump>),
    LitInt(i64),
    LitBool(bool),
    LitStr(Name<'bump>),
    PrimOp(PrimOp),
    Universe(Universe),
    /// Language builtins (int, bool, str, data, prop, theorem, proof, and, or, not, implies).
    Builtin(Name<'bump>),
    /// Parser-level identifier, resolved by desugar to either a local `Var` or a free `Global`.
    Named(Name<'bump>),
    /// Desugared free symbol (top-level definitions, constructors, projectors).
    Global(Name<'bump>),
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
    ByProof(Option<&'bump Term<'bump>>, &'bump [Tactic<'bump>]),
    AutoProof,
    RefParam,
    /// Enum type definition (in `prop`): (name, [(variant_name, [(field_name, constraint)])])
    EnumDef(
        Name<'bump>,
        &'bump [(Name<'bump>, &'bump [(Name<'bump>, &'bump Term<'bump>)])],
    ),
    /// Variant constructor (in `data`): (enum_name, variant_index, payload_values)
    Variant(Name<'bump>, usize, &'bump [&'bump Term<'bump>]),
    /// Pattern match elimination (in `data`): (scrutinee, [(var_idx, [(bind_name, bind_type)], body)])
    Match(&'bump Term<'bump>, &'bump [MatchBranch<'bump>]),
    /// Parser-level pattern match before constructor names are resolved.
    NamedMatch(&'bump Term<'bump>, &'bump [NamedMatchBranch<'bump>]),
    /// Parser-level sequential effect block. Desugared to `Let` before checking/codegen.
    Do(&'bump [DoStmt<'bump>]),
    /// Explicit unsafe boundary. It does not change the term's constraint or effect.
    Unsafe(&'bump Term<'bump>),
    /// Explicit IO elimination, valid only inside an unsafe boundary.
    Pure(&'bump Term<'bump>),
    /// Struct type definition (in `prop`): (name, [(field_name, constraint)])
    StructDef(Name<'bump>, &'bump [(Name<'bump>, &'bump Term<'bump>)]),
    /// Struct value construction (in `data`): (struct_name, field_values in order)
    StructCons(Name<'bump>, &'bump [&'bump Term<'bump>]),
    /// Struct field projection (in `data`): (subject, field_index)
    StructProj(&'bump Term<'bump>, usize),
    /// Parser-level implicit method call receiver: `receiver.method`.
    MethodCall(&'bump Term<'bump>, Name<'bump>),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::pool::TermArena;

    fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(bumpalo::Bump::new()));
        (b, TermArena::new(b))
    }

    fn bin<'bump>(
        arena: &TermArena<'bump>,
        op: PrimOp,
        l: &'bump Term<'bump>,
        r: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        arena.app(arena.app(arena.prim_op(op), l), r)
    }

    #[test]
    fn primop_apply() {
        let cases: &[(PrimOp, i64, i64, Term<'static>)] = &[
            (PrimOp::Add, 3, 5, Term::LitInt(8)),
            (PrimOp::Sub, 10, 3, Term::LitInt(7)),
            (PrimOp::Sub, 3, 10, Term::LitInt(-7)),
            (PrimOp::Mul, 4, 5, Term::LitInt(20)),
            (PrimOp::Mul, 0, 100, Term::LitInt(0)),
            (PrimOp::Mul, -3, 4, Term::LitInt(-12)),
            (PrimOp::Div, 10, 3, Term::LitInt(3)),
            (PrimOp::Div, 10, 0, Term::LitInt(0)),
            (PrimOp::Div, -10, 3, Term::LitInt(-3)),
            (PrimOp::Mod_, 10, 3, Term::LitInt(1)),
            (PrimOp::Mod_, 10, 0, Term::LitInt(0)),
            (PrimOp::Mod_, -10, 3, Term::LitInt(-1)),
            (PrimOp::Eq, 5, 5, Term::LitBool(true)),
            (PrimOp::Eq, 5, 3, Term::LitBool(false)),
            (PrimOp::Lt, 3, 5, Term::LitBool(true)),
            (PrimOp::Lt, 5, 3, Term::LitBool(false)),
            (PrimOp::Lt, 5, 5, Term::LitBool(false)),
            (PrimOp::Gt, 5, 3, Term::LitBool(true)),
            (PrimOp::Gt, 3, 5, Term::LitBool(false)),
            (PrimOp::Le, 3, 5, Term::LitBool(true)),
            (PrimOp::Le, 5, 5, Term::LitBool(true)),
            (PrimOp::Le, 5, 3, Term::LitBool(false)),
            (PrimOp::Ge, 5, 3, Term::LitBool(true)),
            (PrimOp::Ge, 5, 5, Term::LitBool(true)),
            (PrimOp::Ge, 3, 5, Term::LitBool(false)),
            (PrimOp::Neq, 5, 3, Term::LitBool(true)),
            (PrimOp::Neq, 5, 5, Term::LitBool(false)),
        ];
        for &(op, x, y, expected) in cases {
            assert_eq!(op.apply(x, y), expected, "{op:?} {x} {y}");
        }
    }

    #[test]
    fn primop_display_all() {
        for (op, s) in [
            (PrimOp::Add, "+"),
            (PrimOp::Sub, "-"),
            (PrimOp::Mul, "*"),
            (PrimOp::Div, "/"),
            (PrimOp::Mod_, "%"),
            (PrimOp::Eq, "=="),
            (PrimOp::Lt, "<"),
            (PrimOp::Gt, ">"),
            (PrimOp::Le, "<="),
            (PrimOp::Ge, ">="),
            (PrimOp::Neq, "/="),
        ] {
            assert_eq!(op.to_string(), s);
        }
    }

    #[test]
    fn universe_display_all() {
        for (u, s) in [
            (Universe::UData, "data"),
            (Universe::UProp, "prop"),
            (Universe::UTheorem, "theorem"),
            (Universe::UProof, "proof"),
        ] {
            assert_eq!(u.to_string(), s);
        }
    }

    #[test]
    fn map_preserves_unchanged_nodes() {
        let (_b, arena) = a();
        let term = arena.app(arena.lam(arena.var(0)), arena.lit_int(5));
        let result = arena.map(term, &|_| None);
        assert_eq!(*result, *term);
    }

    #[test]
    fn map_replace_refparam() {
        let (_b, arena) = a();
        let pred = bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0));
        let result = arena.map(pred, &|t| {
            if matches!(t, Term::RefParam) {
                Some(arena.lit_int(5))
            } else {
                None
            }
        });
        assert_eq!(
            *result,
            *bin(&arena, PrimOp::Ge, arena.lit_int(5), arena.lit_int(0))
        );
    }

    #[test]
    fn lit_str_roundtrip() {
        let (_b, arena) = a();
        let s = arena.alloc_str("hello");
        let t = Term::LitStr(s);
        match t {
            Term::LitStr(name) => assert_eq!(name, "hello"),
            _ => panic!("expected LitStr"),
        }
    }
}
