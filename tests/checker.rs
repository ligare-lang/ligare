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

fn check_empty<'bump>(
    arena: &TermArena<'bump>,
    t: &'bump Term<'bump>,
    c: &'bump Term<'bump>,
) -> Result<(), String> {
    check(arena, &empty_table(), &empty_ctx(), t, c)
}

#[test]
fn int_literal() {
    let (_b, arena) = a();
    assert_eq!(
        check_empty(&arena, &Term::LitInt(5), arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn bool_literal() {
    let (_b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            &Term::LitBool(true),
            arena.builtin(s(&arena, "bool"))
        ),
        Ok(())
    );
}

#[test]
fn int_fails_for_bool() {
    let (_b, arena) = a();
    assert!(check_empty(&arena, &Term::LitInt(5), arena.builtin(s(&arena, "bool"))).is_err());
}

#[test]
fn lambda_int_to_int() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("\\x. x", b, &arena),
            parse_constraint("int -> int", b, &arena)
        ),
        Ok(())
    );
}

#[test]
fn lambda_bool_to_int_with_if() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("\\x. (if x then 0 else 1)", b, &arena),
            parse_constraint("bool -> int", b, &arena)
        ),
        Ok(())
    );
}

#[test]
fn if_branches_checked() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("if true then 5 else 3", b, &arena),
            arena.builtin(s(&arena, "int"))
        ),
        Ok(())
    );
}

#[test]
fn let_with_constraint() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("let x : int := 5 in x", b, &arena),
            arena.builtin(s(&arena, "int"))
        ),
        Ok(())
    );
}

#[test]
fn unknown_constraint_fails() {
    let (_b, arena) = a();
    assert!(check_empty(&arena, &Term::LitInt(5), arena.builtin(s(&arena, "foo"))).is_err());
}

#[test]
fn let_with_by_check() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("let x : int by true := 5 in x", b, &arena),
            arena.builtin(s(&arena, "int"))
        ),
        Ok(())
    );
}

#[test]
fn refinement_auto_proof() {
    let (b, arena) = a();
    let term = parse("let y : int where (x => x >= 0) := 42 in y", b, &arena);
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── Multi-parameter application tests (regression: Pi order bug) ──

/// Build a two-param Func node for testing applications.
fn make_two_param_func<'bump>(
    arena: &'bump TermArena<'bump>,
    param1_type: &'bump Term<'bump>,
    param2_type: &'bump Term<'bump>,
    body: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    let params = &[
        (s(arena, "a"), Some(param1_type)),
        (s(arena, "b"), Some(param2_type)),
    ];
    arena.func(
        s(arena, "f"),
        arena.alloc_slice(params),
        Some(arena.builtin(s(arena, "int"))),
        &[],
        &[],
        body,
    )
}

/// Build a curried application: f a1 a2
fn app2<'bump>(
    arena: &'bump TermArena<'bump>,
    f: &'bump Term<'bump>,
    a1: &'bump Term<'bump>,
    a2: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    arena.app(arena.app(f, a1), a2)
}

#[test]
fn app_two_params_passes() {
    let (_b, arena) = a();
    let func = make_two_param_func(
        &arena,
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Add, arena.var(1), arena.var(0)),
    );
    let term = app2(&arena, func, arena.lit_int(3), arena.lit_int(5));
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn app_two_params_fails_wrong_first_arg() {
    let (_b, arena) = a();
    let func = make_two_param_func(
        &arena,
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Add, arena.var(1), arena.var(0)),
    );
    // First argument should be int, but we pass bool
    let term = app2(&arena, func, arena.lit_bool(true), arena.lit_int(5));
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

#[test]
fn app_two_params_fails_wrong_second_arg() {
    let (_b, arena) = a();
    let func = make_two_param_func(
        &arena,
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Add, arena.var(1), arena.var(0)),
    );
    // Second argument should be int, but we pass bool
    let term = app2(&arena, func, arena.lit_int(3), arena.lit_bool(false));
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

#[test]
fn app_two_params_with_refinement_passes() {
    let (_b, arena) = a();
    let nonzero = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    let func = make_two_param_func(
        &arena,
        arena.builtin(s(&arena, "int")),
        nonzero,
        bin(&arena, PrimOp::Div, arena.var(1), arena.var(0)),
    );
    // 1 satisfies (x /= 0), 2 satisfies (x /= 0) — both pass
    let term = app2(&arena, func, arena.lit_int(10), arena.lit_int(2));
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn app_two_params_with_refinement_fails_first_arg() {
    let (_b, arena) = a();
    let nonzero = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    // First param is int, second is nonzero. Pass bool as first arg.
    let func = make_two_param_func(
        &arena,
        arena.builtin(s(&arena, "int")),
        nonzero,
        bin(&arena, PrimOp::Div, arena.var(1), arena.var(0)),
    );
    let term = app2(&arena, func, arena.lit_bool(true), arena.lit_int(5));
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

#[test]
fn app_two_params_with_refinement_fails_second_arg_zero() {
    let (_b, arena) = a();
    let nonzero = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    let func = make_two_param_func(
        &arena,
        arena.builtin(s(&arena, "int")),
        nonzero,
        bin(&arena, PrimOp::Div, arena.var(1), arena.var(0)),
    );
    // 0 does NOT satisfy (x /= 0) — should fail
    let term = app2(&arena, func, arena.lit_int(10), arena.lit_int(0));
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

#[test]
fn app_two_params_with_refinement_passes_negative() {
    let (_b, arena) = a();
    let nonzero = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    let func = make_two_param_func(
        &arena,
        arena.builtin(s(&arena, "int")),
        nonzero,
        bin(&arena, PrimOp::Div, arena.var(1), arena.var(0)),
    );
    // -5 does satisfy (x /= 0) — should pass
    let term = app2(
        &arena,
        func,
        arena.lit_int(20),
        bin(&arena, PrimOp::Sub, arena.lit_int(0), arena.lit_int(5)),
    );
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn app_two_params_refinement_ge_zero_rejects_negative() {
    let (_b, arena) = a();
    // Second param: int where (x => x >= 0)
    let nonneg = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
    );
    let func = make_two_param_func(
        &arena,
        arena.builtin(s(&arena, "int")),
        nonneg,
        bin(&arena, PrimOp::Add, arena.var(1), arena.var(0)),
    );
    // First arg 5 is int ✓; second arg -3 fails (x >= 0) ✗
    let term = app2(
        &arena,
        func,
        arena.lit_int(5),
        bin(&arena, PrimOp::Sub, arena.lit_int(0), arena.lit_int(3)),
    );
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

#[test]
fn app_three_params_order_check() {
    let (_b, arena) = a();
    let params = &[
        (s(&arena, "x"), Some(arena.builtin(s(&arena, "int")))),
        (s(&arena, "y"), Some(arena.builtin(s(&arena, "bool")))),
        (s(&arena, "z"), Some(arena.builtin(s(&arena, "int")))),
    ];
    let func = arena.func(
        s(&arena, "f"),
        arena.alloc_slice(params),
        Some(arena.builtin(s(&arena, "int"))),
        &[],
        &[],
        bin(&arena, PrimOp::Add, arena.var(2), arena.var(0)),
    );
    // Correct: int, bool, int
    let term = arena.app(
        arena.app(arena.app(func, arena.lit_int(1)), arena.lit_bool(true)),
        arena.lit_int(2),
    );
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn app_three_params_wrong_middle() {
    let (_b, arena) = a();
    let params = &[
        (s(&arena, "x"), Some(arena.builtin(s(&arena, "int")))),
        (s(&arena, "y"), Some(arena.builtin(s(&arena, "bool")))),
        (s(&arena, "z"), Some(arena.builtin(s(&arena, "int")))),
    ];
    let func = arena.func(
        s(&arena, "f"),
        arena.alloc_slice(params),
        Some(arena.builtin(s(&arena, "int"))),
        &[],
        &[],
        bin(&arena, PrimOp::Add, arena.var(2), arena.var(0)),
    );
    // Wrong: second arg should be bool, but we pass int
    let term = arena.app(
        arena.app(arena.app(func, arena.lit_int(1)), arena.lit_int(42)),
        arena.lit_int(2),
    );
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

// ── Variable checking with context ──

#[test]
fn var_in_context_matches_type() {
    let (_b, arena) = a();
    use ligare::checker::context::{Context, extend_ctx};
    let ctx = extend_ctx(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        &Context::empty(),
    );
    assert_eq!(
        check(
            &arena,
            &empty_table(),
            &ctx,
            arena.var(0),
            arena.builtin(s(&arena, "int"))
        ),
        Ok(())
    );
}

#[test]
fn var_in_context_mismatch_type() {
    let (_b, arena) = a();
    use ligare::checker::context::{Context, extend_ctx};
    let ctx = extend_ctx(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        &Context::empty(),
    );
    assert!(
        check(
            &arena,
            &empty_table(),
            &ctx,
            arena.var(0),
            arena.builtin(s(&arena, "bool"))
        )
        .is_err()
    );
}

#[test]
fn var_from_context_satisfies_refinement() {
    let (_b, arena) = a();
    // Define nat as int where (x => x >= 0)
    let table = add_refine(
        s(&arena, "nat"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    // Check that 5 has type nat when nat is in the table
    assert_eq!(
        check(
            &arena,
            &table,
            &empty_ctx(),
            arena.lit_int(5),
            arena.builtin(s(&arena, "nat"))
        ),
        Ok(())
    );
}

// ── Annot with Pi types (function type annotations) ──

#[test]
fn annot_pi_matches_constraint_pi() {
    let (b, arena) = a();
    // (\x. x : int -> int) checked against int -> int
    let annot = arena.annot(
        parse("\\x. x", b, &arena),
        parse_constraint("int -> int", b, &arena),
    );
    assert_eq!(
        check_empty(&arena, annot, parse_constraint("int -> int", b, &arena)),
        Ok(())
    );
}

#[test]
fn annot_pi_contravariant_domain() {
    let (_b, arena) = a();
    // (\x. 5 : int -> int) checked against data -> int
    // Contravariance: the function's declared domain is int, but
    // the constraint only demands data (which is strictly wider).
    // The body is the constant 5, which satisfies int regardless
    // of x's type.
    let annot = arena.annot(
        arena.lam(arena.lit_int(5)),
        arena.pi(
            s(&arena, ""),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "int")),
        ),
    );
    assert_eq!(
        check_empty(
            &arena,
            annot,
            arena.pi(
                s(&arena, ""),
                arena.builtin(s(&arena, "data")),
                arena.builtin(s(&arena, "int"))
            )
        ),
        Ok(())
    );
}

#[test]
fn annot_pi_mismatch_codomain() {
    let (b, arena) = a();
    // (\x. x : int -> int) checked against int -> bool — codomain mismatch
    let annot = arena.annot(
        parse("\\x. x", b, &arena),
        parse_constraint("int -> int", b, &arena),
    );
    assert!(check_empty(&arena, annot, parse_constraint("int -> bool", b, &arena)).is_err());
}

// ── ByProof ──

#[test]
fn by_proof_passes() {
    let (_b, arena) = a();
    let term = arena.by_proof(arena.lit_int(5), arena.lit_bool(true));
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn by_proof_fails_wrong_type() {
    let (_b, arena) = a();
    let term = arena.by_proof(arena.lit_int(5), arena.lit_bool(true));
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "bool"))).is_err());
}

// ── Logical constraint operators ──

#[test]
fn constraint_and_term_satisfies_both() {
    let (_b, arena) = a();
    // Constraint: (and int (5 > 0)) — 5 satisfies both int and >0
    let constraint_and = arena.app(
        arena.app(
            arena.builtin(s(&arena, "and")),
            arena.builtin(s(&arena, "int")),
        ),
        bin(&arena, PrimOp::Gt, arena.ref_param(), arena.lit_int(0)),
    );
    assert_eq!(
        check_empty(&arena, arena.lit_int(5), constraint_and),
        Ok(())
    );
}

#[test]
fn constraint_or_first_branch_succeeds() {
    let (_b, arena) = a();
    // Constraint: (or bool int) — 5 is not bool, but is int, so passes via second branch
    let constraint_or = arena.app(
        arena.app(
            arena.builtin(s(&arena, "or")),
            arena.builtin(s(&arena, "bool")),
        ),
        arena.builtin(s(&arena, "int")),
    );
    assert_eq!(check_empty(&arena, arena.lit_int(5), constraint_or), Ok(()));
}

#[test]
fn constraint_not_always_passes() {
    let (_b, arena) = a();
    // Constraint: (not bool) — any term passes
    let constraint_not = arena.app(
        arena.builtin(s(&arena, "not")),
        arena.builtin(s(&arena, "bool")),
    );
    assert_eq!(
        check_empty(&arena, arena.lit_int(42), constraint_not),
        Ok(())
    );
}

// ── Zero-param Func (constant definition) ──

#[test]
fn zero_param_func_constant() {
    let (_b, arena) = a();
    // def x : int := 5 → Func with no params, type int, body 5
    let func = arena.func(
        s(&arena, "x"),
        arena.alloc_slice(&[]),
        Some(arena.builtin(s(&arena, "int"))),
        &[],
        &[],
        arena.lit_int(5),
    );
    assert_eq!(
        check_empty(&arena, func, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn zero_param_func_wrong_type_fails() {
    let (_b, arena) = a();
    let func = arena.func(
        s(&arena, "x"),
        arena.alloc_slice(&[]),
        Some(arena.builtin(s(&arena, "int"))),
        &[],
        &[],
        arena.lit_int(5),
    );
    assert!(check_empty(&arena, func, arena.builtin(s(&arena, "bool"))).is_err());
}

// ── Nested Pi types ──

#[test]
fn lambda_with_nested_pi_passes() {
    let (b, arena) = a();
    // (\f. f 1) : (int -> int) -> int
    let term = parse("\\f. f 1", b, &arena);
    let constraint = parse_constraint("(int -> int) -> int", b, &arena);
    assert_eq!(check_empty(&arena, term, constraint), Ok(()));
}

#[test]
fn lambda_with_nested_pi_wrong_codomain_fails() {
    let (b, arena) = a();
    // (\f. f 1) : (int -> int) -> bool — result should be int, not bool
    let term = parse("\\f. f 1", b, &arena);
    let constraint = parse_constraint("(int -> int) -> bool", b, &arena);
    assert!(check_empty(&arena, term, constraint).is_err());
}

// ── Annotation subtype checking ──

#[test]
fn annot_subtype_passes() {
    let (_b, arena) = a();
    // (5 : int) checked against data — int is subtype of data
    let term = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")));
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "data"))),
        Ok(())
    );
}

#[test]
fn annot_supertype_fails() {
    let (_b, arena) = a();
    // (true : bool) checked against int — bool is not int
    let term = arena.annot(arena.lit_bool(true), arena.builtin(s(&arena, "bool")));
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}
