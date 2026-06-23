//! Integration tests for union types and pattern matching.
//! These tests exercise the full parse → check → eval pipeline.

use bumpalo::Bump;
use ligare::backend::c::emit_c;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    let a = TermArena::new(b);
    (b, a)
}

#[test]
fn union_definition_and_variant_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\n  | Blue\n#check Red : Color\n#check Green : Color\n"
            )
            .is_ok()
    );
}

#[test]
fn union_with_payload_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := union\n  | None\n  | Some of (val : int)\n#check Some 5 : Option\n#check None : Option\n"
            )
            .is_ok()
    );
}

#[test]
fn match_reduces_on_variant() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\n  | Blue\n#check (match Red with | Red => 1 | Green => 2 | Blue => 3) : int\n"
            )
            .is_ok()
    );
}

#[test]
fn eval_match() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\n  | Blue\n#show match Red with | Red => 42 | Green => 0 | Blue => 0\n"
            )
            .is_ok()
    );
}

#[test]
fn match_with_binding_eval() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := union\n  | None\n  | Some of (val : int)\n#show match Some 5 with | None => -1 | Some x => x\n"
            )
            .is_ok()
    );
}

#[test]
fn match_none_eval() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := union\n  | None\n  | Some of (val : int)\n#show match None with | None => 0 | Some x => 1\n"
            )
            .is_ok()
    );
}

#[test]
fn wrong_variant_type_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str("def Color : prop := union\n  | Red\n  | Green\n#check Red : int\n")
            .is_err()
    );
}

#[test]
fn wrong_union_member_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\ndef Shape : prop := union\n  | Circle\n  | Square\n#check Circle : Color\n"
            )
            .is_err()
    );
}

// ── C codegen ──

#[test]
fn codegen_recursive_union_typedef() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Nat : prop := union\n  | Zero\n  | Succ of (pred : Nat)\ndef zero : Nat := Zero\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains("struct Nat* pred;"),
        "typedef missing struct Nat*:\n{c}"
    );
    assert!(c.contains(".Zero = {0}"), "empty variant init wrong:\n{c}");
}

#[test]
fn codegen_recursive_variant_address_of() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Nat : prop := union\n  | Zero\n  | Succ of (pred : Nat)\ndef one : Nat := Succ Zero\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("&((Nat)"), "recursive field missing &:\n{c}");
}

// ── Additional match and union tests (test coverage) ──

#[test]
fn match_nested_variants() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Tree : prop := union\n  | Leaf\n  | Node of (left : Tree) (val : int) (right : Tree)\ndef t : Tree := Node Leaf 1 Leaf\n#check t : Tree\n"
            )
            .is_ok()
    );
}

#[test]
fn match_with_bound_var_eval() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := union\n  | None\n  | Some of (val : int)\n#show match Some 42 with | None => -1 | Some x => x + 1\n"
            )
            .is_ok()
    );
}

#[test]
fn match_all_variants_covered() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\n  | Blue\ndef f (c : Color) : int := match c with | Red => 1 | Green => 2 | Blue => 3\n"
            )
            .is_ok()
    );
}

#[test]
fn match_single_variant_union() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Singleton : prop := union\n  | Only\n#show match Only with | Only => 99\n"
            )
            .is_ok()
    );
}

#[test]
fn recursive_union_match() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Nat : prop := union\n  | Zero\n  | Succ of (pred : Nat)\ndef depth (n : Nat) : int := match n with | Zero => 0 | Succ p => 1 + depth p\n"
            )
            .is_ok()
    );
}

#[test]
fn union_with_mixed_payload_types() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Value : prop := union\n  | IntVal of (n : int)\n  | StrVal of (s : str)\n  | BoolVal of (b : bool)\n#check IntVal 5 : Value\n"
            )
            .is_ok()
    );
}

#[test]
fn match_exhaustiveness_not_required_at_typecheck() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\n  | Blue\ndef f (c : Color) : int := match c with | Red => 1 | Green => 2\n"
            )
            .is_ok()
    );
}

// ── Full-pipeline C codegen tests (compile -> emit_c) ──

#[test]
fn codegen_match_with_binding_emits_decl() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Option : prop := union\n  | None\n  | Some of (val : int)\n#show match Some 42 with | None => -1 | Some x => x\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("int64_t x ="), "missing bind decl:\n{c}");
    assert!(
        c.contains("_s0.data.Some.val"),
        "missing field access:\n{c}"
    );
}

#[test]
fn codegen_multiple_matches_unique_vars() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Color : prop := union\n  | Red\n  | Green\n#show match Red with | Red => 1 | Green => 2\n#show match Green with | Red => 10 | Green => 20\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("_s0"), "missing _s0:\n{c}");
    assert!(c.contains("_s1"), "missing _s1:\n{c}");
    assert!(c.contains("_r0"), "missing _r0:\n{c}");
    assert!(c.contains("_r1"), "missing _r1:\n{c}");
}

#[test]
fn codegen_function_returning_union() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Option : prop := union\n  | None\n  | Some of (val : int)\ndef some_val : Option := Some 42\n#show some_val\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains("const Option some_val"),
        "missing union const:\n{c}"
    );
    assert!(c.contains("Some"), "missing variant in const:\n{c}");
}

#[test]
fn codegen_tagged_union_typedef() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Shape : prop := union\n  | Circle\n  | Square\n  | Triangle\ndef s : Shape := Square\ndef c : Shape := Circle\n#show s\n#show c\n",
        )
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("typedef struct Shape"), "missing typedef:\n{c}");
    assert!(c.contains("int tag;"), "missing tag:\n{c}");
    // Should have both variant names in the typedef
    assert!(c.contains("Circle"), "missing Circle:\n{c}");
    assert!(c.contains("Square"), "missing Square:\n{c}");
    assert!(c.contains("Triangle"), "missing Triangle:\n{c}");
}

#[test]
fn codegen_empty_main_with_no_output() {
    // Library-only files get a dummy main so they still compile.
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str("def Color : prop := union\n  | Red\n  | Green\ndef x : Color := Red\n")
        .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains("int main(void)"),
        "missing main:
{c}"
    );
    assert!(
        c.contains("return 0;"),
        "missing return:
{c}"
    );
    assert!(
        c.contains("typedef struct Color"),
        "missing typedef:
{c}"
    );
    assert!(
        c.contains("const Color x"),
        "missing const:
{c}"
    );
}
