mod common;

use common::{bin, leak_bump, parse, parse_constraint, s};
use ligare::checker::check;
use ligare::checker::context::{add_refine, empty_ctx, empty_table};
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Term};
use ligare::diagnostic::Diagnostic;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

fn nat_def<'a>(arena: &TermArena<'a>) -> (&'a str, &'a Term<'a>, &'a Term<'a>) {
    (
        "Nat",
        arena.builtin(s(arena, "int")),
        bin(arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
    )
}

fn pos_def<'a>(arena: &TermArena<'a>) -> (&'a str, &'a Term<'a>, &'a Term<'a>) {
    (
        "Pos",
        arena.builtin(s(arena, "int")),
        bin(arena, PrimOp::Gt, arena.ref_param(), arena.lit_int(0)),
    )
}

fn check_with<'bump>(
    arena: &TermArena<'bump>,
    refs: &[(&str, &'bump Term<'bump>, &'bump Term<'bump>)],
    t: &'bump Term<'bump>,
    c: &'bump Term<'bump>,
) -> Result<(), Diagnostic> {
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
            arena.builtin(s(&arena, "Nat"))
        ),
        Ok(())
    );
}

#[test]
fn top_level_refinement_alias_registers_constraint() {
    let (b, arena) = a();
    let mut compiler = Compiler::new(b, &arena);
    let result = compiler.process_file_str(
        "def Nat := int where (x => x >= 0)\ndef x : Nat := 10\n#check x : int\n",
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
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
            arena.builtin(s(&arena, "Nat"))
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
            arena.builtin(s(&arena, "Nat"))
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
            arena.builtin(s(&arena, "Pos"))
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
            arena.builtin(s(&arena, "Pos"))
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
            parse("fun x => x", b, &arena),
            parse_constraint("Nat -> int", b, &arena)
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
            parse("fun x => x", b, &arena),
            parse_constraint("Pos -> int", b, &arena)
        ),
        Ok(())
    );
}

// ── Neq (not-equal) refinement ──

#[test]
fn neq_refinement_accepts_nonzero() {
    let (_b, arena) = a();
    let table = add_refine(
        s(&arena, "NonZero"),
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
            arena.builtin(s(&arena, "NonZero"))
        ),
        Ok(())
    );
}

#[test]
fn neq_refinement_rejects_zero() {
    let (_b, arena) = a();
    let table = add_refine(
        s(&arena, "NonZero"),
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
            arena.builtin(s(&arena, "NonZero"))
        )
        .is_err()
    );
}

#[test]
fn neq_refinement_accepts_negative() {
    let (b, arena) = a();
    let table = add_refine(
        s(&arena, "NonZero"),
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
            arena.builtin(s(&arena, "NonZero"))
        ),
        Ok(())
    );
}

// ── New refinement tests ──

/// Even: int where (x => x % 2 == 0)
fn even_def<'a>(arena: &TermArena<'a>) -> (&'a str, &'a Term<'a>, &'a Term<'a>) {
    (
        "Even",
        arena.builtin(s(arena, "int")),
        bin(
            arena,
            PrimOp::Eq,
            bin(arena, PrimOp::Mod_, arena.ref_param(), arena.lit_int(2)),
            arena.lit_int(0),
        ),
    )
}

#[test]
fn even_accepts_4() {
    let (_b, arena) = a();
    let even = even_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[even],
            arena.lit_int(4),
            arena.builtin(s(&arena, "Even"))
        ),
        Ok(())
    );
}

#[test]
fn even_rejects_3() {
    let (_b, arena) = a();
    let even = even_def(&arena);
    assert!(
        check_with(
            &arena,
            &[even],
            arena.lit_int(3),
            arena.builtin(s(&arena, "Even"))
        )
        .is_err()
    );
}

#[test]
fn even_accepts_0() {
    let (_b, arena) = a();
    let even = even_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[even],
            arena.lit_int(0),
            arena.builtin(s(&arena, "Even"))
        ),
        Ok(())
    );
}

#[test]
fn even_accepts_negative_2() {
    let (b, arena) = a();
    let even = even_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[even],
            parse("-2", b, &arena),
            arena.builtin(s(&arena, "Even"))
        ),
        Ok(())
    );
}

#[test]
fn nat_accepts_large_number() {
    let (_b, arena) = a();
    let nat = nat_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[nat],
            arena.lit_int(99999),
            arena.builtin(s(&arena, "Nat"))
        ),
        Ok(())
    );
}

#[test]
fn nat_rejects_large_negative() {
    let (b, arena) = a();
    let nat = nat_def(&arena);
    assert!(
        check_with(
            &arena,
            &[nat],
            parse("-99999", b, &arena),
            arena.builtin(s(&arena, "Nat"))
        )
        .is_err()
    );
}

/// Ten: int where (x => x == 10)
fn ten_def<'a>(arena: &TermArena<'a>) -> (&'a str, &'a Term<'a>, &'a Term<'a>) {
    (
        "Ten",
        arena.builtin(s(arena, "int")),
        bin(arena, PrimOp::Eq, arena.ref_param(), arena.lit_int(10)),
    )
}

#[test]
fn ten_accepts_10() {
    let (_b, arena) = a();
    let ten = ten_def(&arena);
    assert_eq!(
        check_with(
            &arena,
            &[ten],
            arena.lit_int(10),
            arena.builtin(s(&arena, "Ten"))
        ),
        Ok(())
    );
}

#[test]
fn ten_rejects_9() {
    let (_b, arena) = a();
    let ten = ten_def(&arena);
    assert!(
        check_with(
            &arena,
            &[ten],
            arena.lit_int(9),
            arena.builtin(s(&arena, "Ten"))
        )
        .is_err()
    );
}

// ── Multiple refinements in table ──

#[test]
fn multiple_refinements_in_table() {
    let (_b, arena) = a();
    let nat = nat_def(&arena);
    let pos = pos_def(&arena);
    // Both "Nat" and "Pos" in the table
    assert_eq!(
        check_with(
            &arena,
            &[nat, pos],
            arena.lit_int(5),
            arena.builtin(s(&arena, "Nat"))
        ),
        Ok(())
    );
    assert_eq!(
        check_with(
            &arena,
            &[nat, pos],
            arena.lit_int(5),
            arena.builtin(s(&arena, "Pos"))
        ),
        Ok(())
    );
    assert!(
        check_with(
            &arena,
            &[nat, pos],
            arena.lit_int(0),
            arena.builtin(s(&arena, "Pos"))
        )
        .is_err()
    );
}

// ── Refinement chain: A is refinement of B ──

#[test]
fn nat_is_refinement_of_int() {
    let (_b, arena) = a();
    let nat = nat_def(&arena);
    // Anything that satisfies Nat must also be int
    assert_eq!(
        check_with(
            &arena,
            &[nat],
            arena.lit_int(5),
            arena.builtin(s(&arena, "int"))
        ),
        Ok(())
    );
}

// ── Neq refinement with non-zero check ──

#[test]
fn nonzero_rejects_zero_when_neq_used() {
    let (_b, arena) = a();
    let nonzero = (
        "NonZero",
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    assert!(
        check_with(
            &arena,
            &[nonzero],
            arena.lit_int(0),
            arena.builtin(s(&arena, "NonZero"))
        )
        .is_err()
    );
}

#[test]
fn nonzero_accepts_one() {
    let (_b, arena) = a();
    let nonzero = (
        "NonZero",
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    assert_eq!(
        check_with(
            &arena,
            &[nonzero],
            arena.lit_int(1),
            arena.builtin(s(&arena, "NonZero"))
        ),
        Ok(())
    );
}

// ── Le refinement ──

#[test]
fn le_refinement_accepts_equal() {
    let (_b, arena) = a();
    let le_five = (
        "Le5",
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Le, arena.ref_param(), arena.lit_int(5)),
    );
    assert_eq!(
        check_with(
            &arena,
            &[le_five],
            arena.lit_int(5),
            arena.builtin(s(&arena, "Le5"))
        ),
        Ok(())
    );
    assert_eq!(
        check_with(
            &arena,
            &[le_five],
            arena.lit_int(3),
            arena.builtin(s(&arena, "Le5"))
        ),
        Ok(())
    );
    assert!(
        check_with(
            &arena,
            &[le_five],
            arena.lit_int(6),
            arena.builtin(s(&arena, "Le5"))
        )
        .is_err()
    );
}

// ── Lt refinement ──

#[test]
fn lt_refinement_rejects_equal() {
    let (_b, arena) = a();
    let lt_five = (
        "Lt5",
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Lt, arena.ref_param(), arena.lit_int(5)),
    );
    assert_eq!(
        check_with(
            &arena,
            &[lt_five],
            arena.lit_int(4),
            arena.builtin(s(&arena, "Lt5"))
        ),
        Ok(())
    );
    assert!(
        check_with(
            &arena,
            &[lt_five],
            arena.lit_int(5),
            arena.builtin(s(&arena, "Lt5"))
        )
        .is_err()
    );
}
