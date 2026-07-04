//! Tests for the C code generation backend.
//!
//! Tests cover literals, constants, functions with confirmed signatures,
//! function calls, let bindings, and enum/struct codegen.

use crate::backend::c::{CEmitter, CodeGenerator};
use crate::backend::ir::{CType, FunSig};
use crate::core::pool::TermArena;
use crate::core::syntax::{PrimOp, Term};
use crate::front::parser::TopLevel;
use bumpalo::Bump;

// ── Test helpers ──

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    (b, TermArena::new(b))
}

fn sig(name: &str, param_types: Vec<CType>, ret_type: CType) -> (&str, FunSig) {
    let leaked: &'static str = Box::leak(name.to_string().into_boxed_str());
    (
        leaked,
        FunSig {
            param_types,
            ret_type,
        },
    )
}

fn emit(tops: &[TopLevel<'_>], fun_sigs: &[(&str, FunSig)]) -> String {
    let emitter = CEmitter::new(&[], &[], fun_sigs).unwrap();
    emitter.generate(tops, tops, &[], &[]).unwrap()
}

fn emit_eval(tops: &[TopLevel<'_>], fun_sigs: &[(&str, FunSig)]) -> String {
    let emitter = CEmitter::new(&[], &[], fun_sigs).unwrap();
    emitter
        .generate_eval(tops, tops, &[], &[])
        .unwrap()
        .unwrap()
}

fn emit_err(tops: &[TopLevel<'_>], fun_sigs: &[(&str, FunSig)]) -> String {
    let emitter = CEmitter::new(&[], &[], fun_sigs).unwrap();
    emitter.generate(tops, tops, &[], &[]).unwrap_err().message
}

fn emit_eval_err(tops: &[TopLevel<'_>], fun_sigs: &[(&str, FunSig)]) -> String {
    let emitter = CEmitter::new(&[], &[], fun_sigs).unwrap();
    emitter
        .generate_eval(tops, tops, &[], &[])
        .unwrap_err()
        .message
}

fn emit_with_types(
    tops: &[TopLevel<'_>],
    raw_defs: &[TopLevel<'_>],
    fun_sigs: &[(&str, FunSig)],
    enum_types: &[(&str, &Term<'_>)],
    struct_types: &[(&str, &Term<'_>)],
) -> String {
    let emitter = CEmitter::new(struct_types, enum_types, fun_sigs).unwrap();
    emitter
        .generate(tops, raw_defs, struct_types, enum_types)
        .unwrap()
}

fn emit_eval_err_with_types(
    tops: &[TopLevel<'_>],
    raw_defs: &[TopLevel<'_>],
    fun_sigs: &[(&str, FunSig)],
    enum_types: &[(&str, &Term<'_>)],
    struct_types: &[(&str, &Term<'_>)],
) -> String {
    let emitter = CEmitter::new(struct_types, enum_types, fun_sigs).unwrap();
    emitter
        .generate_eval(tops, raw_defs, struct_types, enum_types)
        .unwrap_err()
        .message
}

// ── Literals ──

#[test]
fn int_literal_uses_ld() {
    let (_b, arena) = setup();
    let c = emit_eval(&[TopLevel::TLEval(arena.lit_int(42), 0..0)], &[]);
    assert!(c.contains("42"));
    assert!(c.contains("%ld"));
}

#[test]
fn str_literal_uses_s() {
    let (_b, arena) = setup();
    let c = emit_eval(
        &[TopLevel::TLEval(arena.lit_str(arena.alloc_str("hi")), 0..0)],
        &[],
    );
    assert!(c.contains("\"hi\""));
    assert!(c.contains("%s"));
}

#[test]
fn str_literal_is_c_escaped() {
    let (_b, arena) = setup();
    let c = emit_eval(
        &[TopLevel::TLEval(
            arena.lit_str(arena.alloc_str("a\"b\\c\n")),
            0..0,
        )],
        &[],
    );
    assert!(c.contains("\"a\\\"b\\\\c\\n\""), "{c}");
}

#[test]
fn str_literal_control_escape_is_bounded() {
    let (_b, arena) = setup();
    let c = emit_eval(
        &[TopLevel::TLEval(
            arena.lit_str(arena.alloc_str("a\u{1f}f")),
            0..0,
        )],
        &[],
    );
    assert!(c.contains("\"a\\037f\""), "{c}");
}

#[test]
fn bool_literal_emits_0_or_1() {
    let (_b, arena) = setup();
    let c = emit_eval(&[TopLevel::TLEval(arena.lit_bool(true), 0..0)], &[]);
    assert!(c.contains("(int64_t)(1)"));
}

#[test]
fn final_c_ignores_eval_outputs() {
    let (_b, arena) = setup();
    let c = emit(&[TopLevel::TLEval(arena.lit_int(42), 0..0)], &[]);
    assert!(c.contains("int main(void)"));
    assert!(!c.contains("printf"));
    assert!(!c.contains("%ld"));
}

// ── Constants ──

#[test]
fn int_const_def() {
    let (_b, arena) = setup();
    let name = arena.alloc_str("x");
    let c = emit(
        &[TopLevel::TLDef(name, &[], None, arena.lit_int(5), 0..0)],
        &[],
    );
    assert!(c.contains("const int64_t x = 5;"));
}

#[test]
fn str_const_def() {
    let (_b, arena) = setup();
    let name = arena.alloc_str("g");
    let c = emit(
        &[TopLevel::TLDef(
            name,
            &[],
            None,
            arena.lit_str(arena.alloc_str("hi")),
            0..0,
        )],
        &[],
    );
    assert!(c.contains("const char* g"));
    assert!(c.contains("\"hi\""));
}

// ── Functions without confirmed signatures ──

#[test]
fn lam_function_without_param_types_errors() {
    let (_b, arena) = setup();
    let body = arena.app(
        arena.app(arena.prim_op(PrimOp::Add), arena.var(1)),
        arena.var(0),
    );
    let lam = arena.lam(arena.lam(body));
    let name = arena.alloc_str("add");
    let err = emit_err(&[TopLevel::TLDef(name, &[], None, lam, 0..0)], &[]);
    assert!(err.contains("without explicit parameter types"));
}

#[test]
fn lam_returning_str_without_param_type_errors() {
    let (_b, arena) = setup();
    let lam = arena.lam(arena.lit_str(arena.alloc_str("hi")));
    let name = arena.alloc_str("greet");
    let err = emit_err(&[TopLevel::TLDef(name, &[], None, lam, 0..0)], &[]);
    assert!(err.contains("without explicit parameter types"));
}

// ── Functions WITH FunSig ──

#[test]
fn func_with_str_param_uses_const_char_ptr() {
    let (_b, arena) = setup();
    let name = arena.alloc_str("echo");
    let params: &[(
        crate::core::syntax::Name,
        Option<&crate::core::syntax::Term>,
    )] = arena.alloc_slice(&[(
        arena.alloc_str("s"),
        Some(arena.builtin(arena.alloc_str("str"))),
    )]);
    let desugared = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            arena.alloc_str("s"),
            arena.builtin(arena.alloc_str("str")),
            arena.builtin(arena.alloc_str("str")),
        ),
    );
    let sigs = &[sig("echo", vec![CType::Str], CType::Str)];
    let c = emit(
        &[TopLevel::TLDef(
            name,
            params,
            Some(arena.builtin(arena.alloc_str("str"))),
            desugared,
            0..0,
        )],
        sigs,
    );
    assert!(c.contains("const char* echo(const char* s)"));
}

#[test]
fn func_with_mixed_params() {
    let (_b, arena) = setup();
    let name = arena.alloc_str("f");
    let params: &[(
        crate::core::syntax::Name,
        Option<&crate::core::syntax::Term>,
    )] = arena.alloc_slice(&[
        (
            arena.alloc_str("a"),
            Some(arena.builtin(arena.alloc_str("int"))),
        ),
        (
            arena.alloc_str("b"),
            Some(arena.builtin(arena.alloc_str("str"))),
        ),
    ]);
    let desugared = arena.annot(
        arena.lam(arena.lam(arena.var(1))),
        arena.pi(
            arena.alloc_str("a"),
            arena.builtin(arena.alloc_str("int")),
            arena.pi(
                arena.alloc_str("b"),
                arena.builtin(arena.alloc_str("str")),
                arena.builtin(arena.alloc_str("int")),
            ),
        ),
    );
    let sigs = &[sig("f", vec![CType::Int64, CType::Str], CType::Int64)];
    let c = emit(
        &[TopLevel::TLDef(
            name,
            params,
            Some(arena.builtin(arena.alloc_str("int"))),
            desugared,
            0..0,
        )],
        sigs,
    );
    assert!(c.contains("int64_t f(int64_t a, const char* b)"));
}

// ── Function calls ──

#[test]
fn call_to_function_uses_fun_sig_return_type() {
    let (_b, arena) = setup();
    let fn_name = arena.alloc_str("greet");
    let def = TopLevel::TLDef(
        fn_name,
        &[],
        Some(arena.builtin(arena.alloc_str("str"))),
        arena.annot(
            arena.lit_str(arena.alloc_str("hi")),
            arena.builtin(arena.alloc_str("str")),
        ),
        0..0,
    );
    let sig = FunSig {
        param_types: vec![],
        ret_type: CType::Str,
    };
    let show = TopLevel::TLEval(arena.builtin(fn_name), 0..0);
    let tops = &[def, show];
    let c = emit_eval(tops, &[(fn_name, sig)]);
    assert!(c.contains("%s"));
    assert!(c.contains("const char* greet"));
}

#[test]
fn emit_undefined_func_call_errors() {
    let (_b, arena) = setup();
    let n = arena.alloc_str("s");
    let call = arena.app(arena.builtin(n), arena.lit_str(arena.alloc_str("hi")));
    let tops = &[TopLevel::TLEval(call, 0..0)];
    let err = emit_eval_err(tops, &[]);
    assert!(err.contains("missing function signature"));
}

#[test]
fn emit_let_str_printf_format() {
    let (_b, arena) = setup();
    let term = arena.let_(
        arena.alloc_str("s"),
        arena.lit_str(arena.alloc_str("hi")),
        arena.var(0),
        None,
    );
    let c = emit_eval(&[TopLevel::TLEval(term, 0..0)], &[]);
    assert!(c.contains("%s"));
    assert!(c.contains("const char* s"));
}

#[test]
fn emit_multiple_defs_and_outputs() {
    let (_b, arena) = setup();
    let tops = &[
        TopLevel::TLDef(arena.alloc_str("a"), &[], None, arena.lit_int(1), 0..0),
        TopLevel::TLDef(
            arena.alloc_str("b"),
            &[],
            None,
            arena.lit_str(arena.alloc_str("two")),
            0..0,
        ),
        TopLevel::TLEval(arena.lit_int(3), 0..0),
        TopLevel::TLEval(arena.lit_str(arena.alloc_str("four")), 0..0),
    ];
    let c = emit_eval(tops, &[]);
    assert!(c.contains("const int64_t a = 1;"));
    assert!(c.contains("const char* b = \"two\";"));
    assert!(c.contains("%ld"));
    assert!(c.contains("%s"));
}

// ── Enum codegen ──

/// Build an enum typedef with empty and payload variants.
#[test]
fn enum_typedef_with_recursive_field() {
    let (_b, arena) = setup();
    let nat_name = arena.alloc_str("Nat");
    let zero_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
    let succ_fields: &[(crate::core::syntax::Name, &crate::core::syntax::Term)] =
        arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
    let succ_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Succ"), succ_fields);
    let variants: &[(
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    )] = arena.alloc_slice(&[zero_variant, succ_variant]);
    let nat_udef = arena.enum_def(nat_name, variants);
    let enum_types: &[(&str, &crate::core::syntax::Term)] =
        arena.bump().alloc([(nat_name, nat_udef)]);

    let top_name = arena.alloc_str("zero");
    let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
    let tops = &[TopLevel::TLDef(
        top_name,
        &[],
        Some(arena.builtin(nat_name)),
        zero_v,
        0..0,
    )];

    let c = emit_with_types(tops, tops, &[], enum_types, &[]);
    // Typedef uses a pointer for recursive fields.
    assert!(c.contains("Nat* pred;"), "expected Nat* pred; in:\n{c}");
    // Empty variant uses proper initializer
    assert!(c.contains(".Zero = {0}"), "expected .Zero = {{0}} in:\n{c}");
    // Constant declaration uses enum type name
    assert!(
        c.contains("const Nat zero ="),
        "expected const Nat zero in:\n{c}"
    );
}

#[test]
fn enum_typedef_sanitizes_qualified_type_name() {
    let (_b, arena) = setup();
    let nat_name = arena.alloc_str("std::data::nat::Nat");
    let variants: &[(
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    )] = arena.alloc_slice(&[(arena.alloc_str("Zero"), arena.alloc_slice(&[]))]);
    let nat_udef = arena.enum_def(nat_name, variants);
    let enum_types: &[(&str, &crate::core::syntax::Term)] =
        arena.bump().alloc([(nat_name, nat_udef)]);
    let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
    let tops = &[TopLevel::TLDef(
        arena.alloc_str("zero"),
        &[],
        Some(arena.builtin(nat_name)),
        zero_v,
        0..0,
    )];

    let c = emit_with_types(tops, tops, &[], enum_types, &[]);
    assert!(c.contains("typedef struct std__data__nat__Nat"), "{c}");
    assert!(c.contains("const std__data__nat__Nat zero"), "{c}");
    assert!(!c.contains("struct std::data::nat::Nat"), "{c}");
}

/// Recursive variant construction heap-copies the payload.
#[test]
fn enum_recursive_variant_heap_allocates_payload() {
    let (_b, arena) = setup();
    let nat_name = arena.alloc_str("Nat");
    let zero_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
    let succ_fields: &[(crate::core::syntax::Name, &crate::core::syntax::Term)] =
        arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
    let succ_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Succ"), succ_fields);
    let variants: &[(
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    )] = arena.alloc_slice(&[zero_variant, succ_variant]);
    let nat_udef = arena.enum_def(nat_name, variants);
    let enum_types: &[(&str, &crate::core::syntax::Term)] =
        arena.bump().alloc([(nat_name, nat_udef)]);

    // Build: Succ(Zero)
    let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
    let one_v = arena.variant(nat_name, 1, arena.alloc_slice(&[zero_v]));
    let tops = &[TopLevel::TLDef(
        arena.alloc_str("one"),
        &[],
        Some(arena.builtin(nat_name)),
        one_v,
        0..0,
    )];

    let c = emit_with_types(tops, &[], &[], enum_types, &[]);
    // Recursive fields copy the payload to heap storage instead of taking the
    // address of a temporary value.
    assert!(
        c.contains(".pred = ({ Nat* _ligare_heap"),
        "expected heap-backed recursive field in:\n{c}"
    );
    assert!(
        c.contains("ligare_default_allocate(sizeof(Nat))"),
        "expected allocator call for recursive field in:\n{c}"
    );
    assert!(!c.contains("&((Nat)"), "unexpected address-of in:\n{c}");
}

#[test]
fn unknown_enum_variant_errors() {
    let (_b, arena) = setup();
    let missing_name = arena.alloc_str("Missing");
    let term = arena.variant(missing_name, 0, arena.alloc_slice(&[]));
    let tops = &[TopLevel::TLEval(term, 0..0)];
    let err = emit_eval_err_with_types(tops, tops, &[], &[], &[]);
    assert!(err.contains("unknown enum `Missing`"), "{err}");
}

#[test]
fn enum_variant_payload_count_errors() {
    let (_b, arena) = setup();
    let nat_name = arena.alloc_str("Nat");
    let zero_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
    let succ_fields: &[(crate::core::syntax::Name, &crate::core::syntax::Term)] =
        arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
    let succ_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Succ"), succ_fields);
    let variants: &[(
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    )] = arena.alloc_slice(&[zero_variant, succ_variant]);
    let nat_udef = arena.enum_def(nat_name, variants);
    let enum_types: &[(&str, &crate::core::syntax::Term)] =
        arena.bump().alloc([(nat_name, nat_udef)]);

    let malformed = arena.variant(nat_name, 1, arena.alloc_slice(&[]));
    let tops = &[TopLevel::TLEval(malformed, 0..0)];
    let err = emit_eval_err_with_types(tops, tops, &[], enum_types, &[]);
    assert!(
        err.contains("Variant `Nat.Succ` expects 1 payload(s), got 0"),
        "{err}"
    );
}

#[test]
fn struct_constructor_field_count_errors() {
    let (_b, arena) = setup();
    let pair_name = arena.alloc_str("Pair");
    let fields: &[(crate::core::syntax::Name, &crate::core::syntax::Term)] = arena.alloc_slice(&[
        (
            arena.alloc_str("left"),
            arena.builtin(arena.alloc_str("int")),
        ),
        (
            arena.alloc_str("right"),
            arena.builtin(arena.alloc_str("int")),
        ),
    ]);
    let pair_def = arena.struct_def(pair_name, fields);
    let struct_types: &[(&str, &crate::core::syntax::Term)] =
        arena.bump().alloc([(pair_name, pair_def)]);
    let malformed = arena.struct_cons(pair_name, arena.alloc_slice(&[arena.lit_int(1)]));
    let tops = &[TopLevel::TLEval(malformed, 0..0)];
    let err = emit_eval_err_with_types(tops, tops, &[], &[], struct_types);
    assert!(
        err.contains("Struct `Pair` expects 2 field(s), got 1"),
        "{err}"
    );
}
