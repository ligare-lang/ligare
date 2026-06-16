mod common;

use bumpalo::Bump;
use common::{bin, leak_bump, parse, s};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Term};
use ligare::front::parser::{TopLevel, parse_def_top, parse_expr_top, parse_program};

fn a() -> (&'static Bump, TermArena<'static>) {
    let b = leak_bump();
    let a = TermArena::new(b);
    (b, a)
}

#[test]
fn integer_literal() {
    let (b, a) = a();
    assert_eq!(*parse("42", b, &a), Term::LitInt(42));
}

#[test]
fn boolean_literal() {
    let (b, a) = a();
    assert_eq!(*parse("true", b, &a), Term::LitBool(true));
}

#[test]
fn simple_addition() {
    let (b, arena) = a();
    assert_eq!(
        *parse("1 + 2", b, &arena),
        *bin(&arena, PrimOp::Add, arena.lit_int(1), arena.lit_int(2))
    );
}

#[test]
fn comparison() {
    let (b, arena) = a();
    assert_eq!(
        *parse("3 < 5", b, &arena),
        *bin(&arena, PrimOp::Lt, arena.lit_int(3), arena.lit_int(5))
    );
}

#[test]
fn equality() {
    let (b, arena) = a();
    assert_eq!(
        *parse("1 = 2", b, &arena),
        *bin(&arena, PrimOp::Eq, arena.lit_int(1), arena.lit_int(2))
    );
}

#[test]
fn negative_number() {
    let (b, arena) = a();
    let sub = arena.app(arena.prim_op(PrimOp::Sub), arena.lit_int(0));
    assert_eq!(*parse("-5", b, &arena), *arena.app(sub, arena.lit_int(5)));
}

#[test]
fn if_expression() {
    let (b, arena) = a();
    assert_eq!(
        *parse("if true then 1 else 0", b, &arena),
        *arena.if_then_else(arena.lit_bool(true), arena.lit_int(1), arena.lit_int(0))
    );
}

#[test]
fn let_expression() {
    let (b, arena) = a();
    assert_eq!(
        *parse("let x := 5 in x", b, &arena),
        *arena.let_(s(&arena, "x"), arena.lit_int(5), arena.var(0), None)
    );
}

#[test]
fn let_with_constraint() {
    let (b, arena) = a();
    assert_eq!(
        *parse("let x : int := 5 in x", b, &arena),
        *arena.let_(
            s(&arena, "x"),
            arena.lit_int(5),
            arena.var(0),
            Some(arena.builtin(s(&arena, "int")))
        )
    );
}

#[test]
fn lambda() {
    let (b, a) = a();
    assert_eq!(*parse("\\x. x", b, &a), Term::Lam(&Term::Var(0)));
}

#[test]
fn annot_expression() {
    let (b, arena) = a();
    assert_eq!(
        *parse("(5 : int)", b, &arena),
        *arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")))
    );
}

#[test]
fn arrow_type() {
    let (b, arena) = a();
    assert_eq!(
        *parse("int -> bool", b, &arena),
        *arena.pi(
            s(&arena, ""),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "bool"))
        )
    );
}

#[test]
fn dependent_arrow_type() {
    let (b, arena) = a();
    assert_eq!(
        *parse("(x: int) -> x", b, &arena),
        *arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.var(0)
        )
    );
}

#[test]
fn unbound_name_becomes_builtin() {
    let (b, arena) = a();
    assert_eq!(*parse("foo", b, &arena), *arena.builtin(s(&arena, "foo")));
}

#[test]
fn refine_expression() {
    let (b, arena) = a();
    assert_eq!(
        *parse("int where (x => x >= 0)", b, &arena),
        *arena.refine(
            s(&arena, ""),
            arena.builtin(s(&arena, "int")),
            bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0))
        )
    );
}

#[test]
fn refine_in_let_annotation() {
    let (b, arena) = a();
    let t = parse_expr_top("let y : int where (x => x >= 0) := 42 in y", b, &arena);
    assert!(t.is_ok());
}

#[test]
fn refine_in_def_annotation() {
    let (b, arena) = a();
    let t = parse_def_top("def f (a : int where (x => x > 0)) : int := a", b, &arena);
    assert!(t.is_ok());
}

#[test]
fn def_refinement() {
    let (b, arena) = a();
    let result = parse_def_top("def nat := int where (x => x >= 0)", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "nat");
    assert_eq!(
        *term,
        *arena.refine(
            s(&arena, ""),
            arena.builtin(s(&arena, "int")),
            bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0))
        )
    );
}

#[test]
fn program_with_def_and_check() {
    let (b, arena) = a();
    let result = parse_program("def x : int := 5\n#check x : int", b, &arena);
    assert!(result.is_ok());
    let tops = result.unwrap();
    assert_eq!(tops.len(), 2);
    assert!(matches!(tops[0], TopLevel::TLDef(..)));
    assert!(matches!(tops[1], TopLevel::TLCheck(..)));
}

#[test]
fn program_with_expr() {
    let (b, arena) = a();
    let result = parse_program("1 + 2\n#check 3 : int", b, &arena);
    assert!(result.is_ok());
    let tops = result.unwrap();
    assert_eq!(tops.len(), 2);
    assert!(matches!(tops[0], TopLevel::TLExpr(..)));
    assert!(matches!(tops[1], TopLevel::TLCheck(..)));
}

#[test]
fn program_with_show() {
    let (b, arena) = a();
    let result = parse_program("def x : int := 5\n#show x", b, &arena);
    assert!(result.is_ok());
    let tops = result.unwrap();
    assert_eq!(tops.len(), 2);
    assert!(matches!(tops[0], TopLevel::TLDef(..)));
    assert!(matches!(tops[1], TopLevel::TLShow(..)));
}

#[test]
fn show_simple_expr() {
    let (b, arena) = a();
    let result = parse_program("#show 1 + 2", b, &arena);
    assert!(result.is_ok());
    let tops = result.unwrap();
    assert_eq!(tops.len(), 1);
    assert!(matches!(tops[0], TopLevel::TLShow(..)));
}

#[test]
fn func_one_param() {
    let (b, arena) = a();
    assert!(parse_expr_top("func f (x: int) : int := x + 1", b, &arena).is_ok());
}

#[test]
fn func_three_params() {
    let (b, arena) = a();
    assert!(parse_expr_top("func f (a: int) (b: int) (c: int) : int := a", b, &arena).is_ok());
}

#[test]
fn and_prop_parses() {
    let (b, arena) = a();
    let and_term = arena.builtin(s(&arena, "and"));
    assert_eq!(
        *parse("∧ true false", b, &arena),
        *arena.app(
            arena.app(and_term, arena.lit_bool(true)),
            arena.lit_bool(false)
        )
    );
}

#[test]
fn or_prop_parses() {
    let (b, arena) = a();
    let or_term = arena.builtin(s(&arena, "or"));
    assert_eq!(
        *parse("∨ true false", b, &arena),
        *arena.app(
            arena.app(or_term, arena.lit_bool(true)),
            arena.lit_bool(false)
        )
    );
}

#[test]
fn not_prop_parses() {
    let (b, arena) = a();
    assert_eq!(
        *parse("¬ true", b, &arena),
        *arena.app(arena.builtin(s(&arena, "not")), arena.lit_bool(true))
    );
}

#[test]
fn and_in_expression() {
    let (b, arena) = a();
    let and_term = arena.builtin(s(&arena, "and"));
    let int_term = arena.builtin(s(&arena, "int"));
    let bool_term = arena.builtin(s(&arena, "bool"));
    assert_eq!(
        *parse("∧ int bool", b, &arena),
        *arena.app(arena.app(and_term, int_term), bool_term)
    );
}

#[test]
fn let_with_by() {
    let (b, arena) = a();
    assert_eq!(
        *parse("let x : int by true := 5 in x", b, &arena),
        *arena.let_(
            s(&arena, "x"),
            arena.by_proof(arena.lit_int(5), arena.lit_bool(true)),
            arena.var(0),
            Some(arena.builtin(s(&arena, "int")))
        )
    );
}

#[test]
fn def_simple() {
    let (b, arena) = a();
    let result = parse_def_top("def x : int := 5", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "x");
    assert_eq!(
        *term,
        *arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")))
    );
}

#[test]
fn def_with_params() {
    let (b, arena) = a();
    let result = parse_def_top("def add (a : int) (b : int) : int := a + b", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "add");
    let inner = bin(&arena, PrimOp::Add, arena.var(1), arena.var(0));
    assert_eq!(
        *term,
        *arena.annot(arena.lam(arena.lam(inner)), arena.builtin(s(&arena, "int")))
    );
}

#[test]
fn def_no_ret() {
    let (b, arena) = a();
    let result = parse_def_top("def x := 5", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "x");
    assert_eq!(*term, Term::LitInt(5));
}

// ── Binary operator tests (regression for parse_app_generic hijacking infix ops) ──

#[test]
fn binary_sub_in_lambda_body() {
    let (b, arena) = a();
    // "n - 1" must parse as Sub(Var(0), LitInt(1)), NOT as App(Var(0), Sub(0,1)).
    assert_eq!(
        *parse("\\n. n - 1", b, &arena),
        *arena.lam(bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)))
    );
}

#[test]
fn binary_sub_in_parens_in_lambda() {
    let (b, arena) = a();
    // Parentheses should not change the parse of a binary subtraction.
    assert_eq!(
        *parse("\\n. (n - 1)", b, &arena),
        *arena.lam(bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)))
    );
}

#[test]
fn binary_sub_left_assoc_with_add() {
    let (b, arena) = a();
    // "n - 1 + 2" should be left-associative: (n - 1) + 2
    assert_eq!(
        *parse("\\n. n - 1 + 2", b, &arena),
        *arena.lam(bin(
            &arena,
            PrimOp::Add,
            bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)),
            arena.lit_int(2)
        ))
    );
}

#[test]
fn binary_add_left_assoc_with_sub() {
    let (b, arena) = a();
    // "n + 1 - 2" should be left-associative: (n + 1) - 2
    assert_eq!(
        *parse("\\n. n + 1 - 2", b, &arena),
        *arena.lam(bin(
            &arena,
            PrimOp::Sub,
            bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1)),
            arena.lit_int(2)
        ))
    );
}

#[test]
fn unary_negation_in_lambda() {
    let (b, arena) = a();
    // Unary minus should still normalize to: 0 - n
    let sub = arena.app(arena.prim_op(PrimOp::Sub), arena.lit_int(0));
    assert_eq!(
        *parse("\\n. -n", b, &arena),
        *arena.lam(arena.app(sub, arena.var(0)))
    );
}

#[test]
fn binary_plus_with_unary_negation_rhs() {
    let (b, arena) = a();
    // "n + -1" should be Add(Var(0), Sub(0, 1))
    let sub = arena.app(arena.prim_op(PrimOp::Sub), arena.lit_int(0));
    let neg_one = arena.app(sub, arena.lit_int(1));
    assert_eq!(
        *parse("\\n. n + -1", b, &arena),
        *arena.lam(bin(&arena, PrimOp::Add, arena.var(0), neg_one))
    );
}

#[test]
fn binary_sub_in_application() {
    let (b, arena) = a();
    // "f (n-1)" as a lambda: the inner subtraction must be binary, not hijacked.
    // \n. f (n-1)  →  Lam(App(Builtin(f), Sub(Var(0), LitInt(1))))
    assert_eq!(
        *parse("\\n. f (n - 1)", b, &arena),
        *arena.lam(arena.app(
            arena.builtin(s(&arena, "f")),
            bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1))
        ))
    );
}

#[test]
fn binary_sub_multi_param_lambda() {
    let (b, arena) = a();
    // \n m. n - m  →  Lam(Lam(Sub(Var(1), Var(0))))
    assert_eq!(
        *parse("\\n. \\m. n - m", b, &arena),
        *arena.lam(arena.lam(bin(&arena, PrimOp::Sub, arena.var(1), arena.var(0))))
    );
}

#[test]
fn binary_sub_twice_in_lambda() {
    let (b, arena) = a();
    // \n. n - 1 - 2  →  Lam(Sub(Sub(Var(0), LitInt(1)), LitInt(2)))
    let inner_sub = bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1));
    assert_eq!(
        *parse("\\n. n - 1 - 2", b, &arena),
        *arena.lam(bin(&arena, PrimOp::Sub, inner_sub, arena.lit_int(2)))
    );
}

#[test]
fn all_infix_ops_with_variable() {
    let (b, arena) = a();
    // Test that each infix operator works correctly with a variable LHS.
    // This ensures the "break on infix token" logic in parse_app_generic
    // doesn't break any operator.
    let cases: Vec<(&str, PrimOp)> = vec![
        ("\\n. n + 1", PrimOp::Add),
        ("\\n. n - 1", PrimOp::Sub),
        ("\\n. n * 2", PrimOp::Mul),
        ("\\n. n / 2", PrimOp::Div),
        ("\\n. n % 2", PrimOp::Mod_),
        ("\\n. n < 2", PrimOp::Lt),
        ("\\n. n > 2", PrimOp::Gt),
        ("\\n. n <= 2", PrimOp::Le),
        ("\\n. n >= 2", PrimOp::Ge),
        ("\\n. n == 2", PrimOp::Eq),
        ("\\n. n /= 2", PrimOp::Neq),
    ];
    for (input, op) in cases {
        let expected = arena.lam(bin(&arena, op, arena.var(0), arena.lit_int(2)));
        // "n + 1" uses 1, not 2, as the RHS
        let expected = if input.contains("+ 1") || input.contains("- 1") {
            arena.lam(bin(&arena, op, arena.var(0), arena.lit_int(1)))
        } else {
            expected
        };
        assert_eq!(
            *parse(input, b, &arena),
            *expected,
            "failed for input: {}",
            input
        );
    }
}

#[test]
fn def_with_binary_sub_in_body() {
    let (b, arena) = a();
    // Regression: "n - 1" inside a def body must be binary subtraction.
    let result = parse_def_top("def dec (n : int) : int := n - 1", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "dec");
    assert_eq!(
        *term,
        *arena.annot(
            arena.lam(bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1))),
            arena.builtin(s(&arena, "int"))
        )
    );
}

#[test]
fn fib_def_parses_successfully() {
    let (b, arena) = a();
    // The original bug: fib's else branch "fib (n-1) + fib (n-2)" was
    // parsing n-1 as n(0-1) instead of n-1.
    let result = parse_def_top(
        "def fib (n : int) : int := if n < 2 then n else fib (n-1) + fib (n-2)",
        b,
        &arena,
    );
    assert!(result.is_ok());
}

#[test]
fn fib_def_structure_matches_expected() {
    let (b, arena) = a();
    // Full structural test for the fib definition.
    let result = parse_def_top(
        "def fib (n : int) : int := if n < 2 then n else fib (n-1) + fib (n-2)",
        b,
        &arena,
    );
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "fib");

    // Expected: Annot(Lam(IfThenElse(cond, then_, else_)), int)
    let cond = bin(&arena, PrimOp::Lt, arena.var(0), arena.lit_int(2));
    let then_branch = arena.var(0);
    // fib (n-1)  →  App(This, Sub(Var(0), LitInt(1)))
    let rec_call_1 = arena.app(
        arena.this_(),
        bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1)),
    );
    // fib (n-2)  →  App(This, Sub(Var(0), LitInt(2)))
    let rec_call_2 = arena.app(
        arena.this_(),
        bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(2)),
    );
    // fib (n-1) + fib (n-2)
    let else_branch = bin(&arena, PrimOp::Add, rec_call_1, rec_call_2);

    let body = arena.if_then_else(cond, then_branch, else_branch);
    let expected = arena.annot(arena.lam(body), arena.builtin(s(&arena, "int")));

    assert_eq!(*term, *expected);
}

#[test]
fn unary_negation_after_binary_op() {
    let (b, arena) = a();
    // "1 + -2" should treat the second "-" as unary negation.
    let sub = arena.app(arena.prim_op(PrimOp::Sub), arena.lit_int(0));
    let neg_two = arena.app(sub, arena.lit_int(2));
    assert_eq!(
        *parse("1 + -2", b, &arena),
        *bin(&arena, PrimOp::Add, arena.lit_int(1), neg_two)
    );
}

#[test]
fn unary_negation_after_comparison() {
    let (b, arena) = a();
    // "1 < -2" should still parse: unary minus on RHS.
    let sub = arena.app(arena.prim_op(PrimOp::Sub), arena.lit_int(0));
    let neg_two = arena.app(sub, arena.lit_int(2));
    assert_eq!(
        *parse("1 < -2", b, &arena),
        *bin(&arena, PrimOp::Lt, arena.lit_int(1), neg_two)
    );
}

#[test]
fn comparison_of_two_binary_subs() {
    let (b, arena) = a();
    // \n m. n - 1 < m - 2  —  both sides are binary subtractions.
    let left = bin(&arena, PrimOp::Sub, arena.var(1), arena.lit_int(1));
    let right = bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(2));
    assert_eq!(
        *parse("\\n. \\m. n - 1 < m - 2", b, &arena),
        *arena.lam(arena.lam(bin(&arena, PrimOp::Lt, left, right)))
    );
}

#[test]
fn parens_respect_binary_op() {
    let (b, arena) = a();
    // "(n - 1) * 2" inside a lambda — parens should group the subtraction,
    // then binary multiply on the grouped result.
    let sub = bin(&arena, PrimOp::Sub, arena.var(0), arena.lit_int(1));
    assert_eq!(
        *parse("\\n. (n - 1) * 2", b, &arena),
        *arena.lam(bin(&arena, PrimOp::Mul, sub, arena.lit_int(2)))
    );
}
