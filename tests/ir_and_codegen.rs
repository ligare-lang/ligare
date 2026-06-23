//! Unit tests for IR types and C codegen edge cases.

use bumpalo::Bump;
use ligare::backend::c::emit_c;
use ligare::backend::ir::{CType, FunSig, constraint_to_ctype};
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Term};
use std::collections::HashSet;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    (b, TermArena::new(b))
}

fn s<'bump>(arena: &TermArena<'bump>, s: &str) -> &'bump str {
    arena.alloc_str(s)
}

// ── constraint_to_ctype ──

#[test]
fn constraint_int_is_int64() {
    let names = HashSet::new();
    assert_eq!(
        constraint_to_ctype(&Term::Builtin("int"), &names, &names).unwrap(),
        CType::Int64
    );
}

#[test]
fn constraint_str_is_str() {
    let names = HashSet::new();
    assert_eq!(
        constraint_to_ctype(&Term::Builtin("str"), &names, &names).unwrap(),
        CType::Str
    );
}

#[test]
fn constraint_union_name_returns_union() {
    let names: HashSet<String> = ["MyUnion".into()].into();
    let empty = HashSet::new();
    assert_eq!(
        constraint_to_ctype(&Term::Builtin("MyUnion"), &names, &empty).unwrap(),
        CType::Union("MyUnion".into())
    );
}

#[test]
fn constraint_struct_name_returns_struct() {
    let names: HashSet<String> = ["Point".into()].into();
    let empty = HashSet::new();
    assert_eq!(
        constraint_to_ctype(&Term::Builtin("Point"), &empty, &names).unwrap(),
        CType::Struct("Point".into())
    );
}

#[test]
fn constraint_lam_defaults_to_int64() {
    let names = HashSet::new();
    assert_eq!(
        constraint_to_ctype(&Term::Lam(&Term::Var(0)), &names, &names).unwrap(),
        CType::Int64
    );
}

#[test]
fn constraint_var_is_int64() {
    let names = HashSet::new();
    assert_eq!(
        constraint_to_ctype(&Term::Var(0), &names, &names).unwrap(),
        CType::Int64
    );
}

// ── FunSig::from_func ──

#[test]
fn funsig_zero_params_default_ret() {
    let (_b, arena) = setup();
    let sig = FunSig::from_func(
        &[],
        None,
        arena.lit_int(42),
        &HashSet::new(),
        &HashSet::new(),
    )
    .unwrap();
    assert!(sig.param_types.is_empty());
    assert_eq!(sig.ret_type, CType::Int64);
}

#[test]
fn funsig_with_str_param() {
    let (_b, arena) = setup();
    let params: &[(&str, Option<&Term>)] =
        arena.alloc_slice(&[(s(&arena, "s"), Some(arena.builtin(s(&arena, "str"))))]);
    let sig =
        FunSig::from_func(params, None, arena.var(0), &HashSet::new(), &HashSet::new()).unwrap();
    assert_eq!(sig.param_types, vec![CType::Str]);
}

#[test]
fn funsig_with_autoproof_defaults_to_int64() {
    let (_b, arena) = setup();
    let params: &[(&str, Option<&Term>)] =
        arena.alloc_slice(&[(s(&arena, "x"), Some(arena.auto_proof()))]);
    let sig =
        FunSig::from_func(params, None, arena.var(0), &HashSet::new(), &HashSet::new()).unwrap();
    assert_eq!(sig.param_types, vec![CType::Int64]);
}

// ── C codegen: match with str payload ──

#[test]
fn codegen_match_with_str_payload() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Msg : prop := union\n  | Text of (s : str)\n  | Code of (n : int)\n#show match Text \"hi\" with | Text s => s | Code n => \"err\"\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("const char*"), "missing str support:\n{c}");
}

// ── C codegen: multiple unions ──

#[test]
fn codegen_multiple_unions() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def A : prop := union\n  | A1\n  | A2\ndef B : prop := union\n  | B1\n  | B2\ndef a : A := A1\ndef b : B := B2\n#show a\n#show b\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("typedef struct A"), "missing typedef A:\n{c}");
    assert!(c.contains("typedef struct B"), "missing typedef B:\n{c}");
    assert!(c.contains("const A a"), "missing const A:\n{c}");
    assert!(c.contains("const B b"), "missing const B:\n{c}");
}

// ── C codegen: function with match body ──

#[test]
fn codegen_function_with_match_body() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Color : prop := union\n  | Red\n  | Green\ndef f (c : Color) : int := match c with | Red => 1 | Green => 2\n#show f Red\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("int64_t f(Color"), "missing fun sig:\n{c}");
    assert!(c.contains("switch"), "missing switch in fun body:\n{c}");
}

// ── C codegen: wildcard match ──

#[test]
fn codegen_wildcard_match_no_decl() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Opt : prop := union\n  | None\n  | Some of (val : int)\n#show match Some 7 with | None => 0 | Some _ => 1\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    // Should NOT declare the wildcard variable
    assert!(
        !c.contains("int64_t _ ="),
        "wildcard should not be declared:\n{c}"
    );
}

// ── C codegen: constant with match ──

#[test]
fn codegen_constant_constructed_from_match() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Color : prop := union\n  | Red\n  | Green\ndef x : Color := Red\n#show x\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("const Color x"), "missing const:\n{c}");
    assert!(c.contains("printf"), "missing printf:\n{c}");
}

// ── eval_with_self: recursive functions ──

#[test]
fn eval_with_self_fib() {
    use ligare::core::eval::eval_with_self;
    let (_b, arena) = setup();
    // Build: fib = λn. if n < 2 then n else fib(n-1) + fib(n-2)
    let body = arena.if_then_else(
        arena.app(
            arena.app(arena.prim_op(PrimOp::Lt), arena.var(0)),
            arena.lit_int(2),
        ),
        arena.var(0),
        arena.app(
            arena.app(
                arena.prim_op(PrimOp::Add),
                arena.app(
                    arena.builtin(s(&arena, "fib")),
                    arena.app(
                        arena.app(arena.prim_op(PrimOp::Sub), arena.var(0)),
                        arena.lit_int(1),
                    ),
                ),
            ),
            arena.app(
                arena.builtin(s(&arena, "fib")),
                arena.app(
                    arena.app(arena.prim_op(PrimOp::Sub), arena.var(0)),
                    arena.lit_int(2),
                ),
            ),
        ),
    );
    let fib_lam = arena.lam(body);
    assert_eq!(
        *eval_with_self(
            &arena,
            arena.app(fib_lam, arena.lit_int(5)),
            s(&arena, "fib")
        )
        .unwrap(),
        Term::LitInt(5) // fib(5) = 5
    );
    assert_eq!(
        *eval_with_self(
            &arena,
            arena.app(fib_lam, arena.lit_int(10)),
            s(&arena, "fib")
        )
        .unwrap(),
        Term::LitInt(55) // fib(10) = 55
    );
}

#[test]
fn eval_without_self_name_does_not_resolve_recursion() {
    use ligare::core::eval::eval;
    let (_b, arena) = setup();
    // Without self_name, Builtin("fib") stays unresolved
    let body = arena.if_then_else(
        arena.app(
            arena.app(arena.prim_op(PrimOp::Lt), arena.var(0)),
            arena.lit_int(2),
        ),
        arena.var(0),
        arena.app(arena.builtin(s(&arena, "fib")), arena.lit_int(1)),
    );
    let lam = arena.lam(body);
    let result = eval(&arena, arena.app(lam, arena.lit_int(0))).unwrap();
    assert_eq!(*result, Term::LitInt(0)); // base case works
    // With arg=5, it would evaluate if-then-else but Builtin("fib") stays
    let result2 = eval(&arena, arena.app(lam, arena.lit_int(3))).unwrap();
    // Should be stuck due to unresolved Builtin("fib")
    assert!(!matches!(result2, Term::LitInt(_)));
}

// ── Error cases ──

#[test]
fn variant_of_wrong_union_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    // Red belongs to Color, not Shape
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\ndef Shape : prop := union\n  | Circle\n#check Red : Shape\n"
            )
            .is_err()
    );
}

#[test]
fn check_int_as_union_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str("def Color : prop := union\n  | Red\n#check 42 : Color\n")
            .is_err()
    );
}

#[test]
fn parse_error_propagates() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(compiler.process_file_str("def x := @@@\n").is_err());
}
