//! Unit tests for IR types and C codegen edge cases.

use bumpalo::Bump;
use ligare::backend::c::{emit_c, emit_eval_c};
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
fn constraint_enum_name_returns_enum() {
    let names: HashSet<String> = ["MyEnum".into()].into();
    let empty = HashSet::new();
    assert_eq!(
        constraint_to_ctype(&Term::Global("MyEnum"), &names, &empty).unwrap(),
        CType::Enum("MyEnum".into())
    );
}

#[test]
fn constraint_struct_name_returns_struct() {
    let names: HashSet<String> = ["Point".into()].into();
    let empty = HashSet::new();
    assert_eq!(
        constraint_to_ctype(&Term::Global("Point"), &empty, &names).unwrap(),
        CType::Struct("Point".into())
    );
}

#[test]
fn constraint_lam_errors() {
    let names = HashSet::new();
    let err = constraint_to_ctype(&Term::Lam(&Term::Var(0)), &names, &names).unwrap_err();
    assert!(err.message.contains("Cannot map constraint"));
}

#[test]
fn constraint_var_errors() {
    let names = HashSet::new();
    let err = constraint_to_ctype(&Term::Var(0), &names, &names).unwrap_err();
    assert!(err.message.contains("Cannot map constraint"));
}

#[test]
fn constraint_ptr_returns_pointer_type() {
    let (_b, arena) = setup();
    let names = HashSet::new();
    let ptr_c_int = arena.app(
        arena.builtin(s(&arena, "ptr")),
        arena.builtin(s(&arena, "c_int")),
    );
    assert_eq!(
        constraint_to_ctype(ptr_c_int, &names, &names).unwrap(),
        CType::Ptr(Box::new(CType::CInt))
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
fn funsig_variant_body_infers_enum_return_type() {
    let (_b, arena) = setup();
    let body = arena.variant(s(&arena, "Nat"), 0, arena.alloc_slice(&[]));
    let enum_names: HashSet<String> = ["Nat".into()].into();
    let sig = FunSig::from_func(&[], None, body, &enum_names, &HashSet::new()).unwrap();
    assert_eq!(sig.ret_type, CType::Enum("Nat".into()));
}

#[test]
fn funsig_with_unmappable_param_errors() {
    let (_b, arena) = setup();
    let params: &[(&str, Option<&Term>)] =
        arena.alloc_slice(&[(s(&arena, "x"), Some(arena.auto_proof()))]);
    let err = FunSig::from_func(params, None, arena.var(0), &HashSet::new(), &HashSet::new())
        .unwrap_err();
    assert!(err.message.contains("Cannot map constraint"));
}

#[test]
fn funsig_with_missing_param_constraint_errors() {
    let (_b, arena) = setup();
    let params: &[(&str, Option<&Term>)] = arena.alloc_slice(&[(s(&arena, "x"), None)]);
    let err = FunSig::from_func(params, None, arena.var(0), &HashSet::new(), &HashSet::new())
        .unwrap_err();
    assert!(err.message.contains("without an explicit constraint"));
}

// ── C codegen: match with str payload ──

#[test]
fn codegen_match_with_str_payload() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Msg : prop := enum\n  | Text of (s : str)\n  | Code of (n : int)\n#eval match Text \"hi\" with | Text s => s | Code n => \"err\"\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("const char*"), "missing str support:\n{c}");
}

#[test]
fn codegen_ptr_cast_emits_c_cast() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str("def cast (p : ptr c_int) : ptr c_uint := unsafe { ptr_cast c_uint p }\n")
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("unsigned int* cast(int* p)"), "{c}");
    assert!(c.contains("((unsigned int*)p)"), "{c}");
    assert!(!c.contains("ptr_cast("), "{c}");
}

// ── C codegen: multiple enums ──

#[test]
fn codegen_multiple_enums() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def A : prop := enum\n  | A1\n  | A2\ndef B : prop := enum\n  | B1\n  | B2\ndef a : A := A1\ndef b : B := B2\n#eval a\n#eval b\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
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
            "def Color : prop := enum\n  | Red\n  | Green\ndef f (c : Color) : int := match c with | Red => 1 | Green => 2\n#eval f Red\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
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
            "def Opt : prop := enum\n  | None\n  | Some of (val : int)\n#eval match Some 7 with | None => 0 | Some _ => 1\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
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
            "def Color : prop := enum\n  | Red\n  | Green\ndef x : Color := Red\n#eval x\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
    let eval_c = emit_eval_c(compiler.codegen_input())
        .unwrap_or_else(|e| panic!("{e}"))
        .unwrap();
    assert!(c.contains("const Color x"), "missing const:\n{c}");
    assert!(
        !c.contains("printf"),
        "final C should not print evals:\n{c}"
    );
    assert!(eval_c.contains("printf"), "missing eval printf:\n{eval_c}");
}

// ── eval_with_self: recursive functions ──

#[test]
fn eval_with_self_fib() {
    use ligare::core::eval::eval_with_self;
    let (_b, arena) = setup();
    // Build: fib = fun n => if n < 2 then n else fib(n-1) + fib(n-2)
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
fn variant_of_wrong_enum_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    // Red belongs to Color, not Shape
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := enum\n  | Red\ndef Shape : prop := enum\n  | Circle\n#check Red : Shape\n"
            )
            .is_err()
    );
}

#[test]
fn check_int_as_enum_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str("def Color : prop := enum\n  | Red\n#check 42 : Color\n")
            .is_err()
    );
}

#[test]
fn parse_error_propagates() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let err = compiler
        .process_file_str("def x := @@@\n")
        .expect_err("invalid token should fail");
    assert!(err.message.contains("invalid token `@`"), "{}", err.message);
}

#[test]
fn diagnostic_display_includes_source_context() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let err = compiler
        .process_file_str("def ok := 1\n#check true : int\n")
        .expect_err("constraint mismatch should fail");
    let rendered = err.to_string();
    assert!(rendered.contains("<str>:2:1"), "{rendered}");
    assert!(rendered.contains("#check true : int"), "{rendered}");
    assert!(rendered.contains("^"), "{rendered}");
}

#[test]
fn codegen_extern_call_is_direct_c_call() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "extern def c_abs (x : int) : int\n\
             def main : int := unsafe { c_abs 7 }\n\
             main\n",
        )
        .unwrap();
    let codegen = compiler.codegen_input();
    let c = emit_c(codegen).unwrap();
    assert!(
        c.contains("extern int64_t c_abs(int64_t);"),
        "missing extern prototype:\n{c}"
    );
    assert!(c.contains("c_abs(7)"), "missing direct call:\n{c}");
    assert!(
        !c.contains("int64_t c_abs(int64_t) {"),
        "extern should not emit a wrapper definition:\n{c}"
    );
}

#[test]
fn codegen_io_extern_uses_inner_c_repr() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "extern def c_read : IO int\n\
             def main : IO int := do\n  x <- unsafe { c_read }\n  x\n\
             main\n",
        )
        .unwrap();
    let codegen = compiler.codegen_input();
    let c = emit_c(codegen).unwrap();
    assert!(c.contains("extern int64_t c_read();"), "{c}");
    assert!(c.contains("c_read()"), "{c}");
}
