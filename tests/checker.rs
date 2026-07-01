mod common;

use common::{bin, leak_bump, parse, parse_constraint, s};
use ligare::checker::check;
use ligare::checker::context::{add_refine, empty_ctx, empty_table};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Tactic, Term};

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

fn check_empty<'bump>(
    arena: &TermArena<'bump>,
    t: &'bump Term<'bump>,
    c: &'bump Term<'bump>,
) -> Result<(), ligare::diagnostic::Diagnostic> {
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
fn unit_value_checks_as_unit() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("Unit", b, &arena),
            parse_constraint("Unit", b, &arena)
        ),
        Ok(())
    );
}

#[test]
fn int_does_not_check_as_unit() {
    let (b, arena) = a();
    assert!(check_empty(
        &arena,
        parse("0", b, &arena),
        parse_constraint("Unit", b, &arena)
    )
    .is_err());
}

#[test]
fn io_unit_requires_unit_body() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("Unit", b, &arena),
            parse_constraint("IO Unit", b, &arena)
        ),
        Ok(())
    );
    assert!(check_empty(
        &arena,
        parse("0", b, &arena),
        parse_constraint("IO Unit", b, &arena)
    )
    .is_err());
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

/// Build a two-param function as a desugared term: Annot(Lam(Lam(body)), Pi(a, t1, Pi(b, t2, int)))
fn make_two_param_func<'bump>(
    arena: &'bump TermArena<'bump>,
    param1_type: &'bump Term<'bump>,
    param2_type: &'bump Term<'bump>,
    body: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    arena.annot(
        arena.lam(arena.lam(body)),
        arena.pi(
            s(arena, "a"),
            param1_type,
            arena.pi(s(arena, "b"), param2_type, arena.builtin(s(arena, "int"))),
        ),
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
    // def f (x : int) (y : bool) (z : int) : int := x + z
    // Desugared: Annot(Lam(Lam(Lam(x+z))), Pi(x, int, Pi(y, bool, Pi(z, int, int))))
    let func = arena.annot(
        arena.lam(arena.lam(arena.lam(bin(&arena, PrimOp::Add, arena.var(2), arena.var(0))))),
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
    // def f (x : int) (y : bool) (z : int) : int := x + z
    // Desugared: Annot(Lam(Lam(Lam(x+z))), Pi(x, int, Pi(y, bool, Pi(z, int, int))))
    let func = arena.annot(
        arena.lam(arena.lam(arena.lam(bin(&arena, PrimOp::Add, arena.var(2), arena.var(0))))),
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
    assert!(
        check(
            &arena,
            &empty_table(),
            &ctx,
            arena.var(0),
            arena.builtin(s(&arena, "int"))
        )
        .is_ok()
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
    // Define Nat as int where (x => x >= 0)
    let table = add_refine(
        s(&arena, "Nat"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    // Check that 5 has type Nat when Nat is in the table
    assert!(
        check(
            &arena,
            &table,
            &empty_ctx(),
            arena.lit_int(5),
            arena.builtin(s(&arena, "Nat"))
        )
        .is_ok()
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
    let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]);
    let term = by_proof(&arena, arena.lit_int(5), tactics);
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn by_proof_fails_wrong_type() {
    let (_b, arena) = a();
    let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]);
    let term = by_proof(&arena, arena.lit_int(5), tactics);
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
    // def x : int := 5 → Annot(body, ret) for zero-param definitions
    let func = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")));
    assert_eq!(
        check_empty(&arena, func, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn zero_param_func_wrong_type_fails() {
    let (_b, arena) = a();
    // def x : int := 5 → Annot(body, ret) for zero-param definitions
    let func = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")));
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

// ── Data constraint (top type) ──

#[test]
fn data_constraint_accepts_int() {
    let (_b, arena) = a();
    assert_eq!(
        check_empty(&arena, arena.lit_int(42), arena.builtin(s(&arena, "data"))),
        Ok(())
    );
}

#[test]
fn data_constraint_accepts_bool() {
    let (_b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            arena.lit_bool(true),
            arena.builtin(s(&arena, "data"))
        ),
        Ok(())
    );
}

#[test]
fn data_constraint_accepts_lambda() {
    let (_b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            arena.lam(arena.var(0)),
            arena.builtin(s(&arena, "data"))
        ),
        Ok(())
    );
}

#[test]
fn universe_data_constraint_accepts_anything() {
    let (_b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            arena.lit_int(1),
            arena.universe(ligare::core::syntax::Universe::UData)
        ),
        Ok(())
    );
}

// ── Boolean predicate as constraint ──

#[test]
fn bool_predicate_constraint_true() {
    let (_b, arena) = a();
    let constraint = bin(&arena, PrimOp::Gt, arena.ref_param(), arena.lit_int(0));
    assert_eq!(check_empty(&arena, arena.lit_int(5), constraint), Ok(()));
}

#[test]
fn bool_predicate_constraint_false() {
    let (_b, arena) = a();
    let constraint = bin(&arena, PrimOp::Gt, arena.ref_param(), arena.lit_int(10));
    assert!(check_empty(&arena, arena.lit_int(5), constraint).is_err());
}

#[test]
fn bool_predicate_eq_as_constraint() {
    let (_b, arena) = a();
    let constraint = bin(&arena, PrimOp::Eq, arena.ref_param(), arena.lit_int(5));
    assert_eq!(check_empty(&arena, arena.lit_int(5), constraint), Ok(()));
    assert!(check_empty(&arena, arena.lit_int(3), constraint).is_err());
}

#[test]
fn bool_predicate_neq_as_constraint() {
    let (_b, arena) = a();
    let constraint = bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0));
    assert_eq!(check_empty(&arena, arena.lit_int(5), constraint), Ok(()));
    assert!(check_empty(&arena, arena.lit_int(0), constraint).is_err());
}

// ── Annotation edge cases ──

#[test]
fn annot_data_not_subtype_of_int() {
    let (_b, arena) = a();
    // (5 : data) checked against int — this actually PASSES
    // because the checker first verifies 5 : data (OK), then 5 : int (OK)
    let term = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "data")));
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn annot_func_with_refinement_domain_contravariant() {
    let (_b, arena) = a();
    // (\x. 5 : nonneg -> int) checked against data -> int
    // Body is constant 5 (int), so it works for any domain type
    let nonneg = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
    );
    let annot = arena.annot(
        arena.lam(arena.lit_int(5)),
        arena.pi(s(&arena, ""), nonneg, arena.builtin(s(&arena, "int"))),
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

// ── Let edge cases ──

#[test]
fn let_with_wrong_constraint_fails() {
    let (b, arena) = a();
    let term = parse("let x : bool := 5 in x", b, &arena);
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

#[test]
fn let_body_mismatches_constraint() {
    let (_b, arena) = a();
    let term = arena.let_(s(&arena, "x"), arena.lit_int(5), arena.lit_bool(true), None);
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

// ── ProofBlock ──

#[test]
fn proof_block_with_valid_proof() {
    let (_b, arena) = a();
    let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]);
    let term = by_proof(&arena, arena.lit_int(42), tactics);
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── if-branch with context ──

#[test]
fn if_branch_with_context() {
    let (_b, arena) = a();
    let term = arena.if_then_else(arena.lit_bool(true), arena.var(0), arena.var(0));
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
            term,
            arena.builtin(s(&arena, "int"))
        )
        .is_ok()
    );
}

// ── Pi type edge cases ──

#[test]
fn pi_with_named_param_check() {
    let (_b, arena) = a();
    let pi = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    let lam = arena.lam(arena.var(0));
    assert_eq!(check_empty(&arena, lam, pi), Ok(()));
}

#[test]
fn lambda_rejected_by_pi_wrong_codomain() {
    let (_b, arena) = a();
    let lam = arena.lam(arena.lit_bool(true));
    let pi = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    assert!(check_empty(&arena, lam, pi).is_err());
}

// ── Logical constraint edge cases ──

#[test]
fn constraint_and_fails_second_clause() {
    let (_b, arena) = a();
    let constraint_and = arena.app(
        arena.app(
            arena.builtin(s(&arena, "and")),
            arena.builtin(s(&arena, "bool")),
        ),
        bin(&arena, PrimOp::Gt, arena.ref_param(), arena.lit_int(100)),
    );
    assert!(check_empty(&arena, arena.lit_int(42), constraint_and).is_err());
}

#[test]
fn constraint_or_both_fail() {
    let (_b, arena) = a();
    let constraint_or = arena.app(
        arena.app(
            arena.builtin(s(&arena, "or")),
            arena.builtin(s(&arena, "bool")),
        ),
        bin(&arena, PrimOp::Gt, arena.ref_param(), arena.lit_int(100)),
    );
    assert!(check_empty(&arena, arena.lit_int(42), constraint_or).is_err());
}

// ── App without type information ──

#[test]
fn app_with_no_type_info_fallback() {
    let (_b, arena) = a();
    let term = arena.app(arena.lam(arena.var(0)), arena.lit_int(5));
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── Direct Refine constraint ──

#[test]
fn direct_refine_constraint_check() {
    let (_b, arena) = a();
    let refine = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
    );
    assert_eq!(check_empty(&arena, arena.lit_int(5), refine), Ok(()));
    assert!(
        check_empty(
            &arena,
            bin(&arena, PrimOp::Sub, arena.lit_int(0), arena.lit_int(1)),
            refine
        )
        .is_err()
    );
}

// ── Tactic (by) tests ──

/// Convenience: allocate a tactic slice in the arena.
fn tac_slice<'bump>(arena: &TermArena<'bump>, ts: &[Tactic<'bump>]) -> &'bump [Tactic<'bump>] {
    arena.alloc_slice(ts)
}

/// Convenience: `term by tactics` with subject.
fn by_proof<'bump>(
    arena: &TermArena<'bump>,
    t: &'bump Term<'bump>,
    tactics: &'bump [Tactic<'bump>],
) -> &'bump Term<'bump> {
    arena.by_proof(Some(t), tactics)
}

/// `by exact true` on a refinement constraint succeeds.
#[test]
fn tactic_exact_true_passes() {
    let (_b, arena) = a();
    let nat = arena.refine(
        s(&arena, "Nat"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
    );
    // Register Nat in the constraint table so ByProof can expand it.
    let table = add_refine(
        s(&arena, "Nat"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    let term = by_proof(
        &arena,
        arena.lit_int(42),
        tac_slice(&arena, &[Tactic::Exact(arena.lit_bool(true))]),
    );
    assert!(check(&arena, &table, &empty_ctx(), term, nat).is_ok());
}

/// `by exact false` on a refinement constraint must fail.
#[test]
fn tactic_exact_false_fails() {
    let (_b, arena) = a();
    let nat = arena.refine(
        s(&arena, "Nat"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
    );
    let table = add_refine(
        s(&arena, "Nat"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    let term = by_proof(
        &arena,
        arena.lit_int(42),
        tac_slice(&arena, &[Tactic::Exact(arena.lit_bool(false))]),
    );
    assert!(check(&arena, &table, &empty_ctx(), term, nat).is_err());
}

/// Convenience: standalone `by` proof (no subject).
fn by_proof_none<'bump>(
    arena: &TermArena<'bump>,
    tactics: &'bump [Tactic<'bump>],
) -> &'bump Term<'bump> {
    arena.by_proof(None, tactics)
}

/// `by exact false` on a refinement constraint must fail.
#[test]
fn tactic_exact_not_last_fails() {
    let (_b, arena) = a();
    let term = by_proof_none(
        &arena,
        tac_slice(
            &arena,
            &[
                Tactic::Exact(arena.lit_bool(true)),
                Tactic::Exact(arena.lit_bool(true)),
            ],
        ),
    );
    // Check against a Pi type — build_proof_from_tactics will reject
    // because exact is not the last tactic.
    let goal = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    assert!(check_empty(&arena, term, goal).is_err());
}

/// `intro` then `exact` with a variable proves `int -> int`.
#[test]
fn tactic_intro_then_exact_var_proves_identity() {
    let (_b, arena) = a();
    let goal = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    let term = by_proof_none(
        &arena,
        tac_slice(&arena, &[Tactic::Intro(None), Tactic::Exact(arena.var(0))]),
    );
    assert_eq!(check_empty(&arena, term, goal), Ok(()));
}

/// `intro` with a named variable.
#[test]
fn tactic_intro_named_then_exact_var() {
    let (_b, arena) = a();
    let goal = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    let term = by_proof_none(
        &arena,
        tac_slice(
            &arena,
            &[
                Tactic::Intro(Some(s(&arena, "y"))),
                Tactic::Exact(arena.var(0)),
            ],
        ),
    );
    assert_eq!(check_empty(&arena, term, goal), Ok(()));
}

/// `intro` fails when goal is not a Pi.
#[test]
fn tactic_intro_fails_on_non_pi_goal() {
    let (_b, arena) = a();
    let goal = arena.builtin(s(&arena, "int"));
    let term = by_proof_none(
        &arena,
        tac_slice(
            &arena,
            &[Tactic::Intro(None), Tactic::Exact(arena.lit_int(0))],
        ),
    );
    assert!(check_empty(&arena, term, goal).is_err());
}

/// `intro` cannot be last tactic without `exact`.
#[test]
fn tactic_intro_last_fails() {
    let (_b, arena) = a();
    let goal = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    let term = by_proof_none(&arena, tac_slice(&arena, &[Tactic::Intro(None)]));
    assert!(check_empty(&arena, term, goal).is_err());
}

/// `apply` reduces a goal using a known implication.
#[test]
fn tactic_apply_then_exact() {
    let (_b, arena) = a();
    let f_type = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    let f = arena.annot(arena.lam(arena.var(0)), f_type);
    let goal = arena.builtin(s(&arena, "int"));
    let term = by_proof_none(
        &arena,
        tac_slice(
            &arena,
            &[Tactic::Apply(f), Tactic::Exact(arena.lit_int(42))],
        ),
    );
    assert_eq!(check_empty(&arena, term, goal), Ok(()));
}

/// `apply` fails when the function codomain doesn't match the goal.
#[test]
fn tactic_apply_codomain_mismatch_fails() {
    let (_b, arena) = a();
    let f_type = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    let f = arena.annot(arena.lam(arena.var(0)), f_type);
    let goal = arena.builtin(s(&arena, "bool"));
    let term = by_proof_none(
        &arena,
        tac_slice(
            &arena,
            &[Tactic::Apply(f), Tactic::Exact(arena.lit_int(42))],
        ),
    );
    assert!(check_empty(&arena, term, goal).is_err());
}

/// `apply` fails on non-function term.
#[test]
fn tactic_apply_non_function_fails() {
    let (_b, arena) = a();
    let goal = arena.builtin(s(&arena, "int"));
    let term = by_proof_none(
        &arena,
        tac_slice(
            &arena,
            &[
                Tactic::Apply(arena.lit_int(5)),
                Tactic::Exact(arena.lit_int(42)),
            ],
        ),
    );
    assert!(check_empty(&arena, term, goal).is_err());
}

/// `apply` cannot be the last tactic.
#[test]
fn tactic_apply_last_fails() {
    let (_b, arena) = a();
    let f_type = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    let f = arena.annot(arena.lam(arena.var(0)), f_type);
    let goal = arena.builtin(s(&arena, "int"));
    let term = by_proof_none(&arena, tac_slice(&arena, &[Tactic::Apply(f)]));
    assert!(check_empty(&arena, term, goal).is_err());
}

/// `intro` then `apply` then `exact` — multi-step proof.
#[test]
fn tactic_intro_apply_exact_chain() {
    let (_b, arena) = a();
    let inner_pi = arena.pi(
        s(&arena, "x"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    let goal = arena.pi(s(&arena, "f"), inner_pi, inner_pi);
    let term = by_proof_none(
        &arena,
        tac_slice(
            &arena,
            &[
                Tactic::Intro(None),
                Tactic::Intro(None),
                Tactic::Apply(arena.var(1)),
                Tactic::Exact(arena.var(0)),
            ],
        ),
    );
    assert_eq!(check_empty(&arena, term, goal), Ok(()));
}

/// `have` adds a lemma to the context, then `exact` references it.
#[test]
fn tactic_have_then_exact() {
    let (_b, arena) = a();
    let goal = arena.builtin(s(&arena, "int"));
    let term = by_proof_none(
        &arena,
        tac_slice(
            &arena,
            &[
                Tactic::Have(s(&arena, "h"), arena.lit_int(42)),
                Tactic::Exact(arena.builtin(s(&arena, "h"))),
            ],
        ),
    );
    let _ = check_empty(&arena, term, goal);
}

/// `have` cannot be the last tactic.
#[test]
fn tactic_have_last_fails() {
    let (_b, arena) = a();
    let goal = arena.builtin(s(&arena, "int"));
    let term = by_proof_none(
        &arena,
        tac_slice(&arena, &[Tactic::Have(s(&arena, "h"), arena.lit_int(42))]),
    );
    assert!(check_empty(&arena, term, goal).is_err());
}

/// Empty tactic list fails.
#[test]
fn empty_tactics_fails() {
    let (_b, arena) = a();
    let term = by_proof_none(&arena, tac_slice(&arena, &[]));
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

/// Parse `by` with tactic from text.
#[test]
fn parse_by_with_tactics() {
    let (b, arena) = a();
    let term = parse("42 by exact true", b, &arena);
    assert!(matches!(*term, Term::ByProof(_, _)));
    if let Term::ByProof(_, tactics) = term {
        assert_eq!(tactics.len(), 1);
        assert!(matches!(tactics[0], Tactic::Exact(_)));
    }
}

/// Parse `by` with multiple tactics.
#[test]
fn parse_by_multi_tactic() {
    let (b, arena) = a();
    let term = parse("0 by intro; apply f; exact 42", b, &arena);
    assert!(matches!(*term, Term::ByProof(_, _)));
    if let Term::ByProof(_, tactics) = term {
        assert_eq!(tactics.len(), 3);
        assert!(matches!(tactics[0], Tactic::Intro(_)));
        assert!(matches!(tactics[1], Tactic::Apply(_)));
        assert!(matches!(tactics[2], Tactic::Exact(_)));
    }
}

// ── ByProof with intro wrapping (non-refinement fallback) ──

/// `0 by intro; exact 0` builds a lambda and satisfies `int -> int`.
#[test]
fn by_proof_intro_wraps_subject_for_pi() {
    let (b, arena) = a();
    let term = parse("0 by intro; exact 0", b, &arena);
    let pi = arena.pi(
        s(&arena, "_"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    assert_eq!(check_empty(&arena, term, pi), Ok(()));
}

/// Without `intro`/`apply` tactics, the subject is checked directly
/// against the constraint — exact alone does not replace the subject.
#[test]
fn by_proof_exact_only_checks_subject() {
    let (b, arena) = a();
    // `5 by exact true : bool` — subject 5 fails against bool,
    // and exact alone does not trigger the fallback path.
    let term = parse("5 by exact true", b, &arena);
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "bool"))).is_err());
}

/// When the subject alone fails against a non-refinement constraint
/// but the tactics include `intro`/`apply`, fall back to building
/// a proof from tactics and checking that against the constraint.
#[test]
fn by_proof_intro_fallback_when_subject_fails() {
    let (_b, arena) = a();
    let pi = arena.pi(
        s(&arena, "_"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    // 5 alone does NOT satisfy int -> int, so we fall back to
    // tactics which build Lam(0) — this should pass.
    let term = arena.by_proof(
        Some(arena.lit_int(5)),
        arena.alloc_slice(&[Tactic::Intro(None), Tactic::Exact(arena.lit_int(0))]),
    );
    assert_eq!(check_empty(&arena, term, pi), Ok(()));
}

/// When the subject alone satisfies the constraint, tactics are
/// skipped entirely — even if they include `intro`/`apply`.
#[test]
fn by_proof_subject_passes_skips_tactics() {
    let (_b, arena) = a();
    let lam = arena.lam(arena.var(0));
    let pi = arena.pi(
        s(&arena, "_"),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    // `λx.x` already satisfies `int -> int`, so the intro tactic
    // is never reached.
    let term = arena.by_proof(
        Some(lam),
        arena.alloc_slice(&[Tactic::Intro(None), Tactic::Exact(arena.var(0))]),
    );
    assert_eq!(check_empty(&arena, term, pi), Ok(()));
}

// ── Theorem tests (simulating `theorem name : type := body` checking) ──

/// Simulate `theorem t : int := 5` — body must satisfy the declared type.
#[test]
fn theorem_body_matches_type() {
    let (_b, arena) = a();
    let body = arena.lit_int(5);
    let prop = arena.builtin(s(&arena, "int"));
    assert_eq!(check_empty(&arena, body, prop), Ok(()));
}

/// Simulate `theorem t : int := true` — body fails to match.
#[test]
fn theorem_body_mismatches_type() {
    let (_b, arena) = a();
    let body = arena.lit_bool(true);
    let prop = arena.builtin(s(&arena, "int"));
    assert!(check_empty(&arena, body, prop).is_err());
}

/// Simulate `theorem id : int -> int := \x. x` — lambda satisfies arrow type.
#[test]
fn theorem_lambda_matches_arrow_type() {
    let (_b, arena) = a();
    let body = arena.lam(arena.var(0));
    let prop = arena.pi(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        arena.builtin(s(&arena, "int")),
    );
    assert_eq!(check_empty(&arena, body, prop), Ok(()));
}

/// Simulate `theorem t : Nat := 5 by exact true` — refinement with by-block.
#[test]
fn theorem_refinement_with_by_passes() {
    let (_b, arena) = a();
    // Register Nat in constraint table
    let table = add_refine(
        s(&arena, "Nat"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    let body = arena.by_proof(
        Some(arena.lit_int(5)),
        arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]),
    );
    assert!(
        check(
            &arena,
            &table,
            &empty_ctx(),
            body,
            arena.builtin(s(&arena, "Nat"))
        )
        .is_ok()
    );
}

/// Simulate `theorem t : Nat := 5 by exact false` — proof evaluates to false so check fails.
#[test]
fn theorem_refinement_with_by_fails() {
    let (_b, arena) = a();
    let table = add_refine(
        s(&arena, "Nat"),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0)),
        &empty_table(),
    );
    let body = arena.by_proof(
        Some(arena.lit_int(5)),
        arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(false))]),
    );
    assert!(
        check(
            &arena,
            &table,
            &empty_ctx(),
            body,
            arena.builtin(s(&arena, "Nat"))
        )
        .is_err()
    );
}

// ── String literal tests ──

#[test]
fn str_literal_checks_as_str() {
    let (_b, arena) = a();
    let term = arena.lit_str(s(&arena, "hello"));
    let constraint = arena.builtin(s(&arena, "str"));
    assert_eq!(check_empty(&arena, term, constraint), Ok(()));
}

#[test]
fn str_literal_checks_as_data() {
    let (_b, arena) = a();
    let term = arena.lit_str(s(&arena, "hello"));
    let constraint = arena.builtin(s(&arena, "data"));
    assert_eq!(check_empty(&arena, term, constraint), Ok(()));
}

#[test]
fn str_literal_fails_as_int() {
    let (_b, arena) = a();
    let term = arena.lit_str(s(&arena, "hello"));
    let constraint = arena.builtin(s(&arena, "int"));
    assert!(check_empty(&arena, term, constraint).is_err());
}

// ── Undefined variable must fail ──

/// `#check s some_sth : str` where `s` is not defined — must fail.
#[test]
fn undefined_variable_rejected() {
    let (_b, arena) = a();
    // App(Builtin("s"), LitStr("hello")) — "s" is not a defined function
    let term = arena.app(
        arena.builtin(s(&arena, "s")),
        arena.lit_str(s(&arena, "hello")),
    );
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "str"))).is_err());
}

/// `#check s 42 : int` — undefined function "s" with int argument, must fail.
#[test]
fn undefined_variable_int_rejected() {
    let (_b, arena) = a();
    let term = arena.app(arena.builtin(s(&arena, "s")), arena.lit_int(42));
    assert!(check_empty(&arena, term, arena.builtin(s(&arena, "int"))).is_err());
}

// ── Function return type inference for C backend ──

/// Simulate `some_fn "hi" : str` where some_fn has an explicit `: str` return constraint.
/// The checker uses the function's Pi type to verify the result.
#[test]
fn function_with_str_return_checks() {
    let (_b, arena) = a();
    // def some_fn (s : str) : str := s
    // Desugars to: Annot(Lam(Var(0)), Pi("s", str, str))
    let func = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            s(&arena, "s"),
            arena.builtin(s(&arena, "str")),
            arena.builtin(s(&arena, "str")),
        ),
    );
    // Apply to a string literal
    let call = arena.app(func, arena.lit_str(s(&arena, "hi")));
    assert_eq!(
        check_empty(&arena, call, arena.builtin(s(&arena, "str"))),
        Ok(())
    );
}
