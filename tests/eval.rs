mod common;

use common::{bin, leak_bump, parse, s};
use ligare::core::eval::{eval, eval_with_self};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Tactic, Term};

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn integer_identity() {
    let (_b, arena) = a();
    assert_eq!(*eval(&arena, &Term::LitInt(42)).unwrap(), Term::LitInt(42));
}

#[test]
fn boolean_identity() {
    let (_b, arena) = a();
    assert_eq!(
        *eval(&arena, &Term::LitBool(true)).unwrap(),
        Term::LitBool(true)
    );
}

#[test]
fn arithmetic() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("1 + 2 * 3", b, &arena)).unwrap(),
        Term::LitInt(7)
    );
}

#[test]
fn if_true() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("if true then 10 else 20", b, &arena)).unwrap(),
        Term::LitInt(10)
    );
}

#[test]
fn if_false() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("if false then 10 else 20", b, &arena)).unwrap(),
        Term::LitInt(20)
    );
}

#[test]
fn let_() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("let x := 5 in x + 3", b, &arena)).unwrap(),
        Term::LitInt(8)
    );
}

#[test]
fn beta_reduction() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("(fun x => x + 1) 5", b, &arena)).unwrap(),
        Term::LitInt(6)
    );
}

#[test]
fn annot_strips_annotation() {
    let (_b, arena) = a();
    assert_eq!(
        *eval(
            &arena,
            arena.annot(arena.lit_int(42), arena.builtin(s(&arena, "int")))
        )
        .unwrap(),
        Term::LitInt(42)
    );
}

#[test]
fn by_proof_strips_proof() {
    let (_b, arena) = a();
    let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]);
    assert_eq!(
        *eval(&arena, arena.by_proof(Some(arena.lit_int(42)), tactics)).unwrap(),
        Term::LitInt(42)
    );
}

#[test]
fn arithmetic_on_bool_fails() {
    let (_b, arena) = a();
    let result = eval(
        &arena,
        bin(&arena, PrimOp::Add, arena.lit_bool(true), arena.lit_int(1)),
    );
    assert!(result.is_err());
}

#[test]
fn nested_if() {
    let (b, arena) = a();
    assert_eq!(
        *eval(
            &arena,
            parse("if (if true then false else true) then 1 else 2", b, &arena)
        )
        .unwrap(),
        Term::LitInt(2)
    );
}

#[test]
fn func_desugars_and_evaluates() {
    let (_b, arena) = a();
    // def f (x : int) : int := x + 1
    // Desugared: Annot(Lam(Var(0) + 1), Pi("x", int, int))
    let desugared = arena.annot(
        arena.lam(bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1))),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "int")),
        ),
    );
    let app = arena.app(desugared, arena.lit_int(5));
    assert_eq!(*eval(&arena, app).unwrap(), Term::LitInt(6));
}

#[test]
fn let_with_by_proof_evaluates() {
    let (_b, arena) = a();
    let term = arena.let_(
        s(&arena, "x"),
        arena.lit_int(5),
        arena.var(0),
        Some(arena.builtin(s(&arena, "int"))),
    );
    assert_eq!(*eval(&arena, term).unwrap(), Term::LitInt(5));
}

#[test]
fn if_then_else_div_zero_returns_zero() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("if false then (1 / 0) else 42", b, &arena)).unwrap(),
        Term::LitInt(42)
    );
}

#[test]
fn div_zero_returns_zero() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("5 / 0", b, &arena)).unwrap(),
        Term::LitInt(0)
    );
}

#[test]
fn mod_zero_returns_zero() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("5 % 0", b, &arena)).unwrap(),
        Term::LitInt(0)
    );
}

// ── New edge case tests ──

#[test]
fn all_comparison_operators() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("3 < 5", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
    assert_eq!(
        *eval(&arena, parse("5 > 3", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
    assert_eq!(
        *eval(&arena, parse("3 <= 5", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
    assert_eq!(
        *eval(&arena, parse("5 >= 3", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
    assert_eq!(
        *eval(&arena, parse("3 == 3", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
    assert_eq!(
        *eval(&arena, parse("3 /= 5", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
}

#[test]
fn arithmetic_precedence() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("2 + 3 * 4", b, &arena)).unwrap(),
        Term::LitInt(14)
    );
    assert_eq!(
        *eval(&arena, parse("2 * 3 + 4", b, &arena)).unwrap(),
        Term::LitInt(10)
    );
    assert_eq!(
        *eval(&arena, parse("10 - 2 - 3", b, &arena)).unwrap(),
        Term::LitInt(5)
    );
}

#[test]
fn negative_numbers() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("-5", b, &arena)).unwrap(),
        Term::LitInt(-5)
    );
    assert_eq!(
        *eval(&arena, parse("-5 + 3", b, &arena)).unwrap(),
        Term::LitInt(-2)
    );
}

#[test]
fn nested_let() {
    let (b, arena) = a();
    assert_eq!(
        *eval(
            &arena,
            parse("let x := 5 in let y := x + 1 in y * 2", b, &arena)
        )
        .unwrap(),
        Term::LitInt(12)
    );
}

#[test]
fn let_shadowing() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("let x := 5 in let x := 10 in x", b, &arena)).unwrap(),
        Term::LitInt(10)
    );
}

#[test]
fn multiple_beta_nested_lambdas() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("(fun x => fun y => x + y) 3 4", b, &arena)).unwrap(),
        Term::LitInt(7)
    );
}

#[test]
fn multi_param_lambda_beta() {
    let (b, arena) = a();
    // (fun x y => x + y) 3 4 → 7
    assert_eq!(
        *eval(&arena, parse("(fun x y => x + y) 3 4", b, &arena)).unwrap(),
        Term::LitInt(7)
    );
}

#[test]
fn multi_param_lambda_three_params() {
    let (b, arena) = a();
    // (fun x y z => x + y + z) 1 2 3 → 6
    assert_eq!(
        *eval(&arena, parse("(fun x y z => x + y + z) 1 2 3", b, &arena)).unwrap(),
        Term::LitInt(6)
    );
}

#[test]
fn multi_param_lambda_identity_curried() {
    let (b, arena) = a();
    // (fun x y => x) 5 10 → 5
    assert_eq!(
        *eval(&arena, parse("(fun x y => x) 5 10", b, &arena)).unwrap(),
        Term::LitInt(5)
    );
}

// ── fun lambda eval ──

#[test]
fn fun_lam_beta() {
    let (b, arena) = a();
    // (fun x => x + 1) 5 → 6
    assert_eq!(
        *eval(&arena, parse("(fun x => x + 1) 5", b, &arena)).unwrap(),
        Term::LitInt(6)
    );
}

#[test]
fn fun_lam_multi_param_beta() {
    let (b, arena) = a();
    // (fun x y => x + y) 3 4 → 7
    assert_eq!(
        *eval(&arena, parse("(fun x y => x + y) 3 4", b, &arena)).unwrap(),
        Term::LitInt(7)
    );
}

#[test]
fn fun_lam_constrained_beta() {
    let (b, arena) = a();
    // (fun (x : int) => x) 42 → 42
    assert_eq!(
        *eval(&arena, parse("(fun (x : int) => x) 42", b, &arena)).unwrap(),
        Term::LitInt(42)
    );
}

#[test]
fn fun_lam_mixed_params_beta() {
    let (b, arena) = a();
    // (fun x (y : int) => x + y) 10 20 → 30
    assert_eq!(
        *eval(&arena, parse("(fun x (y : int) => x + y) 10 20", b, &arena)).unwrap(),
        Term::LitInt(30)
    );
}

#[test]
fn fun_lam_nested() {
    let (b, arena) = a();
    // (fun f => f 5) (fun x => x + 1) → 6
    assert_eq!(
        *eval(&arena, parse("(fun f => f 5) (fun x => x + 1)", b, &arena)).unwrap(),
        Term::LitInt(6)
    );
}

#[test]
fn lambda_with_free_var() {
    let (_b, arena) = a();
    // A lambda with a free variable de Bruijn index evaluates to itself
    let lam = arena.lam(arena.var(1));
    assert_eq!(*eval(&arena, lam).unwrap(), *lam);
}

#[test]
fn if_with_computed_condition() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("if 1 + 1 == 2 then 100 else 200", b, &arena)).unwrap(),
        Term::LitInt(100)
    );
}

#[test]
fn if_condition_false_expression() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("if 1 == 2 then 100 else 200", b, &arena)).unwrap(),
        Term::LitInt(200)
    );
}

#[test]
fn if_non_bool_condition_preserves() {
    let (_b, arena) = a();
    // if with a non-bool condition (e.g. integer) cannot be reduced
    let result = eval(
        &arena,
        arena.if_then_else(arena.lit_int(42), arena.lit_int(1), arena.lit_int(2)),
    );
    assert!(result.is_ok());
    // The if-then-else should be preserved since condition is not boolean
    match *result.unwrap() {
        Term::IfThenElse(..) => {}
        _ => panic!("expected IfThenElse"),
    }
}

#[test]
fn proof_block_evaluates_inner() {
    let (_b, arena) = a();
    let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_int(42))]);
    let block = arena.by_proof(Some(arena.lit_int(42)), tactics);
    assert_eq!(*eval(&arena, block).unwrap(), Term::LitInt(42));
}

#[test]
fn ref_param_evaluates_to_itself() {
    let (_b, arena) = a();
    assert_eq!(*eval(&arena, arena.ref_param()).unwrap(), Term::RefParam);
}

#[test]
fn auto_proof_evaluates_to_itself() {
    let (_b, arena) = a();
    assert_eq!(*eval(&arena, arena.auto_proof()).unwrap(), Term::AutoProof);
}

#[test]
fn recursive_fib_evaluates() {
    let (_b, arena) = a();
    // Build: fib = fun n => if n < 2 then n else fib(n-1) + fib(n-2)
    // Using a builtin to refer to self
    let body = arena.if_then_else(
        bin(&arena, PrimOp::Lt, arena.var(0), arena.lit_int(2)),
        arena.var(0),
        bin(
            &arena,
            PrimOp::Add,
            arena.app(
                arena.builtin(s(&arena, "fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)),
            ),
            arena.app(
                arena.builtin(s(&arena, "fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(2)),
            ),
        ),
    );
    let fib_lam = arena.lam(body);
    assert_eq!(
        *eval_with_self(
            &arena,
            arena.app(fib_lam, arena.lit_int(10)),
            s(&arena, "fib")
        )
        .unwrap(),
        Term::LitInt(55)
    );
}

#[test]
fn recursive_fib_base_case_zero() {
    let (_b, arena) = a();
    let body = arena.if_then_else(
        bin(&arena, PrimOp::Lt, arena.var(0), arena.lit_int(2)),
        arena.var(0),
        bin(
            &arena,
            PrimOp::Add,
            arena.app(
                arena.builtin(s(&arena, "fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)),
            ),
            arena.app(
                arena.builtin(s(&arena, "fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(2)),
            ),
        ),
    );
    let fib_lam = arena.lam(body);
    assert_eq!(
        *eval_with_self(
            &arena,
            arena.app(fib_lam, arena.lit_int(0)),
            s(&arena, "fib")
        )
        .unwrap(),
        Term::LitInt(0)
    );
}

#[test]
fn recursive_fib_base_case_one() {
    let (_b, arena) = a();
    let body = arena.if_then_else(
        bin(&arena, PrimOp::Lt, arena.var(0), arena.lit_int(2)),
        arena.var(0),
        bin(
            &arena,
            PrimOp::Add,
            arena.app(
                arena.builtin(s(&arena, "fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)),
            ),
            arena.app(
                arena.builtin(s(&arena, "fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(2)),
            ),
        ),
    );
    let fib_lam = arena.lam(body);
    assert_eq!(
        *eval_with_self(
            &arena,
            arena.app(fib_lam, arena.lit_int(1)),
            s(&arena, "fib")
        )
        .unwrap(),
        Term::LitInt(1)
    );
}

#[test]
fn arithmetic_wrapping() {
    let (_b, arena) = a();
    // Add large numbers to test wrapping behavior
    let result = eval(
        &arena,
        bin(
            &arena,
            PrimOp::Add,
            arena.lit_int(i64::MAX),
            arena.lit_int(1),
        ),
    );
    assert_eq!(*result.unwrap(), Term::LitInt(i64::MAX.wrapping_add(1)));
}

#[test]
fn all_binary_arith_operators() {
    let (_b, arena) = a();
    let ops = [
        (PrimOp::Add, &Term::LitInt(7)),
        (PrimOp::Sub, &Term::LitInt(3)),
        (PrimOp::Mul, &Term::LitInt(10)),
        (PrimOp::Div, &Term::LitInt(2)),
        (PrimOp::Mod_, &Term::LitInt(1)),
    ];
    for &(op, expected) in &ops {
        let expr = bin(&arena, op, arena.lit_int(5), arena.lit_int(2));
        assert_eq!(*eval(&arena, expr).unwrap(), *expected, "operator {:?}", op);
    }
}

#[test]
fn app_with_lambda_result_evaluates() {
    let (_b, arena) = a();
    // ((fun x => x) (fun y => y+1)) 5 -> (fun y => y+1) 5 -> 6
    let id = arena.lam(arena.var(0));
    let add1 = arena.lam(bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1)));
    let app1 = arena.app(id, add1);
    let app2 = arena.app(app1, arena.lit_int(5));
    assert_eq!(*eval(&arena, app2).unwrap(), Term::LitInt(6));
}

#[test]
fn sub_with_zero_parses_as_binary() {
    let (b, arena) = a();
    // "n-1" should parse as binary subtraction, not unary negation of 1
    assert_eq!(
        *eval(&arena, parse("5-1", b, &arena)).unwrap(),
        Term::LitInt(4)
    );
}

#[test]
fn lambda_applied_to_lambda_returns_lambda() {
    let (_b, arena) = a();
    // (fun x => fun y => x) 5 -> fun y => 5
    let k = arena.lam(arena.lam(arena.var(1)));
    let app = arena.app(k, arena.lit_int(5));
    assert_eq!(*eval(&arena, app).unwrap(), Term::Lam(arena.lit_int(5)));
}

// ── String tests ──

#[test]
fn string_identity() {
    let (_b, arena) = a();
    let s = arena.lit_str(arena.alloc_str("hello"));
    assert_eq!(
        *eval(&arena, s).unwrap(),
        Term::LitStr(arena.alloc_str("hello"))
    );
}
