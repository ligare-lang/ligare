mod common;

use common::{bin, leak_bump, s};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Term};
use ligare::pretty::pretty;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn integer() {
    assert_eq!(pretty(&Term::LitInt(42)), "42");
}

#[test]
fn lambda() {
    assert_eq!(pretty(&Term::Lam(&Term::Var(0))), "λ. $0");
}

#[test]
fn if_() {
    let (_bump, arena) = a();
    let t = arena.if_then_else(arena.lit_bool(true), arena.lit_int(1), arena.lit_int(0));
    assert_eq!(pretty(t), "if true then 1 else 0");
}

#[test]
fn let_() {
    let (_bump, arena) = a();
    let t = arena.let_(s(&arena, "x"), arena.lit_int(5), arena.var(0), None);
    assert_eq!(pretty(t), "let x = 5 in $0");
}

#[test]
fn annot() {
    let (_bump, arena) = a();
    let t = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")));
    assert_eq!(pretty(t), "(5 : int)");
}

#[test]
fn refine() {
    let (_bump, arena) = a();
    let pred = bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0));
    let t = arena.refine(s(&arena, ""), arena.builtin(s(&arena, "int")), pred);
    assert_eq!(pretty(t), "int where (x => (x >= 0))");
}

#[test]
fn pi_simple() {
    let (_bump, arena) = a();
    let pi = arena.pi(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    assert_eq!(pretty(pi), "(int -> int)");
}

#[test]
fn pi_named() {
    let (_bump, arena) = a();
    let pi = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    assert_eq!(pretty(pi), "(Pi x : int => int)");
}

#[test]
fn pi_nested() {
    let (_bump, arena) = a();
    let inner = arena.pi(
        s(&arena, ""),
        arena.builtin(s(&arena, "bool")),
        arena.builtin(s(&arena, "int")),
    );
    let outer = arena.pi(s(&arena, ""), arena.builtin(s(&arena, "int")), inner);
    assert_eq!(pretty(outer), "(int -> (bool -> int))");
}

#[test]
fn app_infix() {
    let (_bump, arena) = a();
    let add = bin(&arena, PrimOp::Add, arena.lit_int(1), arena.lit_int(2));
    assert_eq!(pretty(add), "(1 + 2)");
}

#[test]
fn app_prefix() {
    let (_bump, arena) = a();
    let app = arena.app(arena.builtin(s(&arena, "f")), arena.lit_int(42));
    assert_eq!(pretty(app), "(f 42)");
}

#[test]
fn compare_ge() {
    let (_bump, arena) = a();
    assert_eq!(
        pretty(bin(&arena, PrimOp::Ge, arena.lit_int(5), arena.lit_int(3))),
        "(5 >= 3)"
    );
}

#[test]
fn compare_neq() {
    let (_bump, arena) = a();
    assert_eq!(
        pretty(bin(&arena, PrimOp::Neq, arena.lit_int(1), arena.lit_int(0))),
        "(1 /= 0)"
    );
}
