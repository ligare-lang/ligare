#![allow(dead_code)]

use bumpalo::Bump;
use ligare::core::pool::TermArena;
use ligare::core::syntax::{Name, PrimOp, Term};
use ligare::front::parser::parse_expr_top;

/// Leak a Bump to get a 'static arena.  Tests are short-lived so leaking
/// is harmless.
pub fn leak_bump() -> &'static Bump {
    Box::leak(Box::new(Bump::new()))
}

/// Build a binary operator application: `(op l) r`.
pub fn bin<'bump>(
    arena: &TermArena<'bump>,
    op: PrimOp,
    l: &'bump Term<'bump>,
    r: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    let op_app = arena.app(arena.prim_op(op), l);
    arena.app(op_app, r)
}

/// Convenience: allocate a string in the arena.
pub fn s<'bump>(arena: &TermArena<'bump>, s: &str) -> Name<'bump> {
    arena.alloc_str(s)
}

/// Parse an expression using the given bump + arena.
#[track_caller]
pub fn parse<'bump>(
    input: &str,
    _bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> &'bump Term<'bump> {
    parse_expr_top(input, _bump, arena).unwrap_or_else(|e| panic!("parse error in test: {}", e))
}

/// Parse a constraint expression.
#[track_caller]
pub fn parse_constraint<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> &'bump Term<'bump> {
    parse(input, bump, arena)
}
