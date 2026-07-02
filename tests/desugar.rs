mod common;

use common::{bin, leak_bump, s};
use ligare::core::debruijn::Desugarer;
use ligare::core::pool::TermArena;
use ligare::core::syntax::PrimOp;
use ligare::front::parser::parse_expr_top;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn func_one_param_no_ret() {
    let (_bump, arena) = a();
    let term = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "data")),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_one_param_with_ret() {
    let (_bump, arena) = a();
    let term = arena.annot(
        arena.lam(bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1))),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "int")),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_two_params() {
    let (_bump, arena) = a();
    let inner = bin(&arena, PrimOp::Add, arena.var(1), arena.var(0));
    let term = arena.annot(
        arena.lam(arena.lam(inner)),
        arena.pi(
            s(&arena, "a"),
            arena.builtin(s(&arena, "int")),
            arena.pi(
                s(&arena, "b"),
                arena.builtin(s(&arena, "int")),
                arena.builtin(s(&arena, "int")),
            ),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_two_params_refinement() {
    let (_bump, arena) = a();
    let refine = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    let inner = bin(&arena, PrimOp::Div, arena.var(1), arena.var(0));
    let term = arena.annot(
        arena.lam(arena.lam(inner)),
        arena.pi(
            s(&arena, "a"),
            arena.builtin(s(&arena, "int")),
            arena.pi(s(&arena, "b"), refine, arena.builtin(s(&arena, "int"))),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_three_params_order() {
    let (_bump, arena) = a();
    let term = arena.annot(
        arena.lam(arena.lam(arena.lam(arena.var(2)))),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.pi(
                s(&arena, "y"),
                arena.builtin(s(&arena, "bool")),
                arena.pi(
                    s(&arena, "z"),
                    arena.builtin(s(&arena, "int")),
                    arena.builtin(s(&arena, "int")),
                ),
            ),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_no_constraint() {
    let (_bump, arena) = a();
    let term = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "data")),
            arena.builtin(s(&arena, "data")),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn do_block_desugars_to_manual_let_chain() {
    let (b, arena) = a();
    let raw = parse_expr_top(
        "do\n  x <- read_int\n  let y = x + 1\n  write_int y\n  ()",
        b,
        &arena,
    )
    .unwrap();
    let io_unit = arena.app(
        arena.builtin(s(&arena, "IO")),
        arena.builtin(s(&arena, "()")),
    );
    let desugared = Desugarer::new(&arena)
        .try_desugar_with_names_and_effect(raw, &[], io_unit)
        .unwrap();
    let io_data = arena.app(
        arena.builtin(s(&arena, "IO")),
        arena.builtin(s(&arena, "data")),
    );
    let expected = arena.let_(
        s(&arena, "x"),
        arena.global(s(&arena, "read_int")),
        arena.let_(
            s(&arena, "y"),
            bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1)),
            arena.let_(
                s(&arena, "_"),
                arena.app(arena.global(s(&arena, "write_int")), arena.var(0)),
                arena.builtin(s(&arena, "()")),
                Some(io_data),
            ),
            None,
        ),
        Some(io_data),
    );
    assert_eq!(*desugared, *expected);
}
