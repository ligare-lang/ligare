mod common;

use common::{bin, leak_bump, parse, s};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Tactic, Term};
use ligare::core::whnf::whnf;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

// ── Leaf values are already WHNF ──

#[test]
fn integer_identity() {
    let (_b, arena) = a();
    assert_eq!(*whnf(&arena, &Term::LitInt(42)).unwrap(), Term::LitInt(42));
}

#[test]
fn bool_identity() {
    let (_b, arena) = a();
    assert_eq!(
        *whnf(&arena, &Term::LitBool(true)).unwrap(),
        Term::LitBool(true)
    );
}

#[test]
fn prim_op_identity() {
    let (_b, arena) = a();
    assert_eq!(
        *whnf(&arena, &Term::PrimOp(PrimOp::Add)).unwrap(),
        Term::PrimOp(PrimOp::Add)
    );
}

#[test]
fn builtin_identity() {
    let (_b, arena) = a();
    let name = s(&arena, "int");
    assert_eq!(
        *whnf(&arena, arena.builtin(name)).unwrap(),
        Term::Builtin(name)
    );
}

#[test]
fn auto_proof_identity() {
    let (_b, arena) = a();
    assert_eq!(*whnf(&arena, &Term::AutoProof).unwrap(), Term::AutoProof);
}

#[test]
fn ref_param_identity() {
    let (_b, arena) = a();
    assert_eq!(*whnf(&arena, &Term::RefParam).unwrap(), Term::RefParam);
}

#[test]
fn lam_identity() {
    let (_b, arena) = a();
    let lam = arena.lam(arena.var(0));
    assert_eq!(*whnf(&arena, lam).unwrap(), *lam);
}

#[test]
fn pi_identity() {
    let (_b, arena) = a();
    let pi = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.var(0),
    );
    assert_eq!(*whnf(&arena, pi).unwrap(), *pi);
}

// ── Beta reduction ──

#[test]
fn beta_reduction() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("(fun x => x + 1) 5", b, &arena)).unwrap(),
        Term::LitInt(6)
    );
}

#[test]
fn nested_beta() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("(fun x => fun y => x + y) 3 4", b, &arena)).unwrap(),
        Term::LitInt(7)
    );
}

// ── Arithmetic (nested arithmetic fully reduces because all args become LitInt) ──

#[test]
fn arithmetic_add() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("1 + 2", b, &arena)).unwrap(),
        Term::LitInt(3)
    );
}

#[test]
fn arithmetic_nested() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("1 + 2 * 3", b, &arena)).unwrap(),
        Term::LitInt(7)
    );
}

#[test]
fn comparison_true() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("5 > 3", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
}

#[test]
fn comparison_false() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("3 == 5", b, &arena)).unwrap(),
        Term::LitBool(false)
    );
}

#[test]
fn division_zero() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("5 / 0", b, &arena)).unwrap(),
        Term::LitInt(0)
    );
}

// ── All comparison operators ──

#[test]
fn all_comparisons_whnf() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("3 < 5", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
    assert_eq!(
        *whnf(&arena, parse("5 <= 5", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
    assert_eq!(
        *whnf(&arena, parse("5 >= 3", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
    assert_eq!(
        *whnf(&arena, parse("3 /= 5", b, &arena)).unwrap(),
        Term::LitBool(true)
    );
}

// ── If-then-else ──

#[test]
fn if_true() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("if true then 10 else 20", b, &arena)).unwrap(),
        Term::LitInt(10)
    );
}

#[test]
fn if_false() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("if false then 10 else 20", b, &arena)).unwrap(),
        Term::LitInt(20)
    );
}

#[test]
fn if_computed_condition() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("if 1 + 1 == 2 then 100 else 200", b, &arena)).unwrap(),
        Term::LitInt(100)
    );
}

#[test]
fn nested_if() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(
            &arena,
            parse("if (if true then false else true) then 1 else 2", b, &arena)
        )
        .unwrap(),
        Term::LitInt(2)
    );
}

// ── Let ──

#[test]
fn let_() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("let x := 5 in x + 3", b, &arena)).unwrap(),
        Term::LitInt(8)
    );
}

#[test]
fn nested_let() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(
            &arena,
            parse("let x := 5 in let y := x + 1 in y * 2", b, &arena)
        )
        .unwrap(),
        Term::LitInt(12)
    );
}

// ── Annotation and proof stripping ──

#[test]
fn annot_strips_annotation() {
    let (_b, arena) = a();
    assert_eq!(
        *whnf(
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
        *whnf(&arena, arena.by_proof(Some(arena.lit_int(42)), tactics)).unwrap(),
        Term::LitInt(42)
    );
}

// ── Refine ──

#[test]
fn refine_evaluates_children() {
    let (_b, arena) = a();
    let pred = arena.lam(bin(&arena, PrimOp::Ge, arena.var(0), arena.lit_int(0)));
    let annot = arena.annot(arena.lit_int(42), arena.builtin(s(&arena, "int")));
    let refine_inner = arena.refine(s(&arena, "Nat"), annot, pred);
    let result = whnf(&arena, refine_inner).unwrap();
    // After WHNF: the inner Annot is stripped, parent is LitInt(42)
    assert_eq!(
        *result,
        Term::Refine(s(&arena, "Nat"), arena.lit_int(42), pred)
    );
}

// ── Mixed: arithmetic on non-literal terms STOPS ──

#[test]
fn non_literal_primop_stops() {
    let (_b, arena) = a();
    // 1 + (Lam x. x)  should stop because (Lam x. x) is not LitInt
    let id_lam = arena.lam(arena.var(0));
    let expr = bin(&arena, PrimOp::Add, arena.lit_int(1), id_lam);
    let result = whnf(&arena, expr).unwrap();
    // Should be App(App(+, 1), lam) — arithmetic did NOT compute
    match *result {
        Term::App(left, _) => match *left {
            Term::App(prim, lit) => {
                assert!(matches!(*prim, Term::PrimOp(PrimOp::Add)));
                assert_eq!(*lit, Term::LitInt(1));
            }
            _ => panic!("unexpected structure"),
        },
        _ => panic!("expected App"),
    }
}

// ── Recursive call via self-reference STOPS (key WHNF behavior) ──

#[test]
fn recursive_call_stops_at_self_ref() {
    let (_b, arena) = a();
    let body = arena.if_then_else(
        bin(&arena, PrimOp::Lt, arena.var(0), arena.lit_int(2)),
        arena.var(0),
        bin(
            &arena,
            PrimOp::Add,
            arena.app(
                arena.builtin(arena.alloc_str("fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)),
            ),
            arena.app(
                arena.builtin(arena.alloc_str("fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(2)),
            ),
        ),
    );
    let lam = arena.lam(body);
    let app = arena.app(lam, arena.lit_int(5));
    let result = whnf(&arena, app).unwrap();

    // The result should NOT be LitInt(5) (fib(5)=5).
    match *result {
        Term::App(..) => {} // stopped — good!
        Term::LitInt(n) => panic!("recursive call was computed: got LitInt({})", n),
        other => panic!("unexpected WHNF form: {:?}", other),
    }
}

#[test]
fn recursive_call_base_case_computes() {
    let (_b, arena) = a();
    let body = arena.if_then_else(
        bin(&arena, PrimOp::Lt, arena.var(0), arena.lit_int(2)),
        arena.var(0),
        bin(
            &arena,
            PrimOp::Add,
            arena.app(
                arena.builtin(arena.alloc_str("fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)),
            ),
            arena.app(
                arena.builtin(arena.alloc_str("fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(2)),
            ),
        ),
    );
    let lam = arena.lam(body);
    let app = arena.app(lam, arena.lit_int(1));
    let result = whnf(&arena, app).unwrap();
    assert_eq!(*result, Term::LitInt(1));
}

#[test]
fn recursive_call_partial_reduction() {
    let (_b, arena) = a();
    let body = arena.if_then_else(
        bin(&arena, PrimOp::Lt, arena.var(0), arena.lit_int(2)),
        arena.var(0),
        bin(
            &arena,
            PrimOp::Add,
            arena.app(
                arena.builtin(arena.alloc_str("fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)),
            ),
            arena.app(
                arena.builtin(arena.alloc_str("fib")),
                bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(2)),
            ),
        ),
    );
    let lam = arena.lam(body);
    let app = arena.app(lam, arena.lit_int(3));
    let result = whnf(&arena, app).unwrap();

    fn contains_self_ref(t: &Term<'_>) -> bool {
        match t {
            Term::Builtin(n) | Term::Global(n) if *n == "fib" => true,
            Term::App(f, a) => contains_self_ref(f) || contains_self_ref(a),
            _ => false,
        }
    }
    assert!(
        contains_self_ref(result),
        "WHNF should preserve self-reference (recursion not unrolled)"
    );
    assert!(
        !matches!(result, Term::LitInt(_)),
        "WHNF should not fully compute fib(3)"
    );
}

// ── Non-recursive function fully evaluates ──

#[test]
fn non_recursive_function_computes() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("(fun x => x + 1) 5", b, &arena)).unwrap(),
        Term::LitInt(6)
    );
}

// ── Non-literal PrimOp gracefully stops (no error) ──

#[test]
fn arithmetic_on_bool_stops_not_errors() {
    let (_b, arena) = a();
    let result = whnf(
        &arena,
        bin(&arena, PrimOp::Add, arena.lit_bool(true), arena.lit_int(1)),
    );
    let term = result.unwrap();
    match *term {
        Term::App(..) => {} // stopped gracefully
        _ => panic!("expected App, got {:?}", term),
    }
}

// ── Func desugaring ──

#[test]
fn func_desugars_to_lambda() {
    let (_b, arena) = a();
    let dom = arena.builtin(s(&arena, "int"));
    let body = bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1));
    // Directly build the desugared form: Annot(Lam(body), Pi("x", int, int))
    let desugared = arena.annot(arena.lam(body), arena.pi(s(&arena, "x"), dom, dom));
    let result = whnf(&arena, desugared).unwrap();
    match *result {
        Term::Lam(_) => {} // correct: Annot(Lam, Pi) → WHNF strips Annot, leaves Lam
        other => panic!("expected Lam from Func desugaring + WHNF, got {:?}", other),
    }
}

// ── New edge case tests ──

#[test]
fn whnf_universe_identity() {
    let (_b, arena) = a();
    let u = arena.universe(ligare::core::syntax::Universe::UProp);
    assert_eq!(
        *whnf(&arena, u).unwrap(),
        Term::Universe(ligare::core::syntax::Universe::UProp)
    );
}

#[test]
fn whnf_var_identity() {
    let (_b, arena) = a();
    assert_eq!(*whnf(&arena, arena.var(3)).unwrap(), Term::Var(3));
}

#[test]
fn whnf_proof_block_strips() {
    let (_b, arena) = a();
    let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_int(42))]);
    let block = arena.by_proof(Some(arena.lit_int(42)), tactics);
    assert_eq!(*whnf(&arena, block).unwrap(), Term::LitInt(42));
}

#[test]
fn whnf_arithmetic_sub() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("10 - 3", b, &arena)).unwrap(),
        Term::LitInt(7)
    );
}

#[test]
fn whnf_arithmetic_mul() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("4 * 5", b, &arena)).unwrap(),
        Term::LitInt(20)
    );
}

#[test]
fn whnf_arithmetic_div() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("10 / 3", b, &arena)).unwrap(),
        Term::LitInt(3)
    );
}

#[test]
fn whnf_arithmetic_mod() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("10 % 3", b, &arena)).unwrap(),
        Term::LitInt(1)
    );
}

#[test]
fn whnf_mod_zero() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("5 % 0", b, &arena)).unwrap(),
        Term::LitInt(0)
    );
}

#[test]
fn whnf_negative_number() {
    let (b, arena) = a();
    assert_eq!(
        *whnf(&arena, parse("-5", b, &arena)).unwrap(),
        Term::LitInt(-5)
    );
}

#[test]
fn whnf_if_non_bool_stops() {
    let (_b, arena) = a();
    let term = arena.if_then_else(arena.lit_int(42), arena.lit_int(1), arena.lit_int(2));
    let result = whnf(&arena, term).unwrap();
    assert!(matches!(*result, Term::IfThenElse(..)));
}

#[test]
fn whnf_let_with_annotation() {
    let (_b, arena) = a();
    // let x : int := 5 in x — annotation on let should not affect WHNF
    let term = arena.let_(
        s(&arena, "x"),
        arena.lit_int(5),
        arena.var(0),
        Some(arena.builtin(s(&arena, "int"))),
    );
    assert_eq!(*whnf(&arena, term).unwrap(), Term::LitInt(5));
}
