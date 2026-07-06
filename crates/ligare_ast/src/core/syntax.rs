use std::fmt;

use crate::config::{
    BUILTIN_AND, BUILTIN_BOOL, BUILTIN_C_INT, BUILTIN_C_UINT, BUILTIN_DATA, BUILTIN_I8,
    BUILTIN_I16, BUILTIN_I32, BUILTIN_I64, BUILTIN_IMPLIES, BUILTIN_INT, BUILTIN_IO, BUILTIN_NOT,
    BUILTIN_OR, BUILTIN_PROOF, BUILTIN_PROP, BUILTIN_PTR, BUILTIN_STR, BUILTIN_THEOREM, BUILTIN_U8,
    BUILTIN_U16, BUILTIN_U32, BUILTIN_U64, BUILTIN_UNIT, UNIVERSE_DATA, UNIVERSE_PROOF,
    UNIVERSE_PROP, UNIVERSE_THEOREM, canonical_builtin_name,
};

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

/// A parser-level struct construction before the target struct and field order
/// are resolved. `None` means the struct type must come from the expected
/// constraint; `Some(name)` is an explicit `Type{field := value}` initializer.
pub type NamedStructFieldInit<'bump> = (Name<'bump>, &'bump Term<'bump>);

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

/// Compute the universe level of a term.
///
/// Levels are compile-time metadata only.  They are intentionally computed from
/// the existing AST instead of being emitted into backend IR or C output.
pub fn compute_level(term: &Term<'_>) -> u32 {
    match term {
        Term::LitInt(_)
        | Term::LitBool(_)
        | Term::LitStr(_)
        | Term::Var(_)
        | Term::Named(_)
        | Term::Global(_)
        | Term::PrimOp(_)
        | Term::RefParam
        | Term::Universe(Universe::UData | Universe::UProp) => 0,
        Term::Universe(Universe::UTheorem | Universe::UProof) => 1,
        Term::Builtin(name) => builtin_level(name),
        Term::App(f, _) => compute_level(f),
        Term::Implicit(inner)
        | Term::Lam(inner)
        | Term::NamedLam(_, inner)
        | Term::Unsafe(inner)
        | Term::Pure(inner)
        | Term::Quote(inner)
        | Term::Splice(inner)
        | Term::StructProj(inner, _)
        | Term::MethodCall(inner, _) => compute_level(inner),
        Term::Pi(_, a, b) | Term::Refine(_, a, b) => {
            compute_level(a).max(compute_level(b)).saturating_add(1)
        }
        Term::Let(_, val, body, constraint) => constraint
            .map(compute_level)
            .unwrap_or(0)
            .max(compute_level(val))
            .max(compute_level(body)),
        Term::IfThenElse(cond, then_branch, else_branch) => compute_level(cond)
            .max(compute_level(then_branch))
            .max(compute_level(else_branch)),
        Term::Annot(term, _) => compute_level(term),
        Term::ByProof(Some(term), tactics) => compute_level(term).max(tactics_level(tactics)),
        Term::ByProof(None, tactics) => 1.max(tactics_level(tactics)),
        Term::AutoProof => 1,
        Term::EnumDef(_, variants) => variants
            .iter()
            .flat_map(|(_, fields)| {
                fields
                    .iter()
                    .map(|(_, constraint)| compute_level(constraint))
            })
            .max()
            .unwrap_or(0)
            .saturating_add(1),
        Term::Variant(_, _, payloads) | Term::StructCons(_, payloads) => payloads
            .iter()
            .map(|payload| compute_level(payload))
            .max()
            .unwrap_or(0),
        Term::NamedStructCons(_, fields) => fields
            .iter()
            .map(|(_, value)| compute_level(value))
            .max()
            .unwrap_or(0),
        Term::Match(scrutinee, branches) => branches
            .iter()
            .map(|(_, binds, body)| {
                binds
                    .iter()
                    .map(|(_, constraint)| compute_level(constraint))
                    .max()
                    .unwrap_or(0)
                    .max(compute_level(body))
            })
            .max()
            .unwrap_or(0)
            .max(compute_level(scrutinee)),
        Term::NamedMatch(scrutinee, branches) => branches
            .iter()
            .map(|(_, binds, body)| {
                binds
                    .iter()
                    .map(|(_, constraint)| compute_level(constraint))
                    .max()
                    .unwrap_or(0)
                    .max(compute_level(body))
            })
            .max()
            .unwrap_or(0)
            .max(compute_level(scrutinee)),
        Term::Do(stmts) => stmts
            .iter()
            .map(|stmt| match stmt {
                DoStmt::Bind(_, rhs) => compute_level(rhs),
                DoStmt::Let(_, rhs, constraint) => {
                    compute_level(rhs).max(constraint.map(compute_level).unwrap_or(0))
                }
                DoStmt::Expr(expr) => compute_level(expr),
            })
            .max()
            .unwrap_or(0),
        Term::StructDef(_, fields) => fields
            .iter()
            .map(|(_, constraint)| compute_level(constraint))
            .max()
            .unwrap_or(0)
            .saturating_add(1),
    }
}

pub fn builtin_level(name: &str) -> u32 {
    match canonical_builtin_name(name) {
        BUILTIN_DATA | BUILTIN_PROP => 0,
        BUILTIN_THEOREM | BUILTIN_PROOF => 1,
        BUILTIN_UNIT => 0,
        BUILTIN_INT | BUILTIN_BOOL | BUILTIN_STR | BUILTIN_IO | BUILTIN_PTR | BUILTIN_AND
        | BUILTIN_OR | BUILTIN_NOT | BUILTIN_IMPLIES | BUILTIN_I8 | BUILTIN_I16 | BUILTIN_I32
        | BUILTIN_I64 | BUILTIN_U8 | BUILTIN_U16 | BUILTIN_U32 | BUILTIN_U64 | BUILTIN_C_INT
        | BUILTIN_C_UINT => 1,
        _ => 0,
    }
}

fn tactics_level(tactics: &[Tactic<'_>]) -> u32 {
    tactics
        .iter()
        .map(|tactic| match tactic {
            Tactic::Exact(term) | Tactic::Apply(term) | Tactic::Have(_, term) => {
                compute_level(term)
            }
            Tactic::Intro(_) => 0,
            Tactic::Custom(_, args) => args.iter().map(|arg| compute_level(arg)).max().unwrap_or(0),
        })
        .max()
        .unwrap_or(0)
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
    /// `name(args...)` — custom compile-time tactic registered with `#[tactic]`.
    Custom(Name<'bump>, &'bump [&'bump Term<'bump>]),
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
    /// Parser-level struct construction by field name, optionally with an
    /// explicit type prefix: `Point{x := 1}` or `{x := 1}`.
    NamedStructCons(Option<Name<'bump>>, &'bump [NamedStructFieldInit<'bump>]),
    /// Struct field projection (in `data`): (subject, field_index)
    StructProj(&'bump Term<'bump>, usize),
    /// Parser-level implicit method call receiver: `receiver.method`.
    MethodCall(&'bump Term<'bump>, Name<'bump>),
    /// Metaprogramming quote: parser-level code quotation.
    Quote(&'bump Term<'bump>),
    /// Metaprogramming splice: compile-time expression insertion.
    Splice(&'bump Term<'bump>),
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
