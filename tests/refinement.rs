mod common;

use common::{bin, leak_bump, parse, parse_constraint, s};
use ligare::checker::check;
use ligare::checker::context::{add_refine, empty_ctx, empty_table};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Term};

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

fn nat_def<'a>(arena: &TermArena<'a>) -> (&'a str, &'a Term<'a>, &'a Term<'a>) {
    (
        "nat",
        arena.builtin(s(arena, "int")),
        bin(arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
    )
}

fn pos_def<'a>(arena: &TermArena<'a>) -> (&'a str, &'a Term<'a>, &'a Term<'a>) {
    (
        "pos",
        arena.builtin(s(arena, "int")),
        bin(arena, PrimOp::Gt, arena.ref_param(), arena.lit_int(0)),
    )
}

fn check_with<'bump>(
    arena: &TermArena<'bump>,
    refs: &[(&str, &'bump Term<'bump>, &'bump Term<'bump>)],
    t: &'bump Term<'bump>,
    c: &'bump Term<'bump>,
) -> Result<(), String> {
    let table = refs
        .iter()
        .fold(empty_table(), |tbl, (n, p, pr)| add_refine(n, p, pr, &tbl));
    check(arena, &table, &empty_ctx(), t, c)
}

#[test]
fn nat_accepts_5() {
    let (_b, arena) = a();
    let nat = nat_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[nat],
            &Term::LitInt(5),
            arena.builtin(s(&arena, "nat"))
        ),
        Ok(())
    );
}

#[test]
fn nat_rejects_negative_1() {
    let (b, arena) = a();
    let nat = nat_def(&arena);
    assert!(
        check_with(
            &arena,
            &[nat],
            parse("-1", b, &arena),
            arena.builtin(s(&arena, "nat"))
        )
        .is_err()
    );
}

#[test]
fn nat_accepts_0() {
    let (_b, arena) = a();
    let nat = nat_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[nat],
            &Term::LitInt(0),
            arena.builtin(s(&arena, "nat"))
        ),
        Ok(())
    );
}

#[test]
fn pos_rejects_0() {
    let (_b, arena) = a();
    let pos = pos_def(&arena);
    assert!(
        check_with(
            &arena,
            &[pos],
            &Term::LitInt(0),
            arena.builtin(s(&arena, "pos"))
        )
        .is_err()
    );
}

#[test]
fn pos_accepts_3() {
    let (_b, arena) = a();
    let pos = pos_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[pos],
            &Term::LitInt(3),
            arena.builtin(s(&arena, "pos"))
        ),
        Ok(())
    );
}

#[test]
fn nat_is_subtype_of_int_variable_check() {
    let (b, arena) = a();
    let nat = nat_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[nat],
            parse("\\x. x", b, &arena),
            parse_constraint("nat -> int", b, &arena)
        ),
        Ok(())
    );
}

#[test]
fn pos_is_subtype_of_int_parent_chain() {
    let (b, arena) = a();
    let pos = pos_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[pos],
            parse("\\x. x", b, &arena),
            parse_constraint("pos -> int", b, &arena)
        ),
        Ok(())
    );
}

// ── Neq (not-equal) refinement ──

#[test]
fn neq_refinement_accepts_nonzero() {
    let (_b, arena) = a();
    let table = add_refine(
        s(&arena, "nonzero"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    assert_eq!(
        check(
            &arena,
            &table,
            &empty_ctx(),
            arena.lit_int(5),
            arena.builtin(s(&arena, "nonzero"))
        ),
        Ok(())
    );
}

#[test]
fn neq_refinement_rejects_zero() {
    let (_b, arena) = a();
    let table = add_refine(
        s(&arena, "nonzero"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    assert!(
        check(
            &arena,
            &table,
            &empty_ctx(),
            arena.lit_int(0),
            arena.builtin(s(&arena, "nonzero"))
        )
        .is_err()
    );
}

#[test]
fn neq_refinement_accepts_negative() {
    let (b, arena) = a();
    let table = add_refine(
        s(&arena, "nonzero"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    let neg_one = parse("-1", b, &arena);
    assert_eq!(
        check(
            &arena,
            &table,
            &empty_ctx(),
            neg_one,
            arena.builtin(s(&arena, "nonzero"))
        ),
        Ok(())
    );
}
