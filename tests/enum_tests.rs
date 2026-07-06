//! Integration tests for enum types and pattern matching.
//! These tests exercise the full parse → check → eval pipeline.

use bumpalo::Bump;
use ligare::backend::c::{emit_c, emit_eval_c};
use ligare::backend::compile::{CompileError, compile_and_run_c};
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    let a = TermArena::new(b);
    (b, a)
}

#[test]
fn enum_definition_and_variant_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := enum\n  | Red\n  | Green\n  | Blue\n#check Red : Color\n#check Green : Color\n"
            )
            .is_ok()
    );
}

#[test]
fn enum_with_payload_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := enum\n  | None\n  | Some of (val : int)\n#check Some 5 : Option\n#check None : Option\n"
            )
            .is_ok()
    );
}

#[test]
fn scoped_enum_constructors_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := enum\n  | Red\n  | Green\ndef Option : prop := enum\n  | None\n  | Some of (val : int)\n#check Color::Red : Color\n#check Option::Some 5 : Option\n#check Option::None : Option\n"
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
                "def Color : prop := enum\n  | Red\n  | Green\n  | Blue\n#check (match Red with | Red => 1 | Green => 2 | Blue => 3) : int\n"
            )
            .is_ok()
    );
}

#[test]
fn match_uses_variant_names_not_branch_order() {
    let (bump, arena) = setup();
    let mut c = Compiler::new(bump, &arena);
    c.process_file_str(
        "def Color : prop := enum\n  | Red\n  | Green\n#check match Red with | Green => false | Red => true : true\n",
    )
    .unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn eval_match() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := enum\n  | Red\n  | Green\n  | Blue\n#eval match Red with | Red => 42 | Green => 0 | Blue => 0\n"
            )
            .is_ok()
    );
}

#[test]
fn scoped_enum_constructors_codegen_and_eval() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Option : prop := enum\n  | None\n  | Some of (val : int)\n#eval match Option::Some 42 with | Option::None => 0 | Option::Some x => x\n",
        )
        .unwrap();
    let eval_c = emit_eval_c(compiler.codegen_input())
        .unwrap_or_else(|e| panic!("{e}"))
        .expect("program has #eval output");
    match compile_and_run_c(&eval_c) {
        Ok(stdout) => assert_eq!(stdout, "42\n"),
        Err(CompileError::CompilerNotFound) => {
            eprintln!("skipping scoped enum constructor native run: C compiler not found")
        }
        Err(err) => panic!("scoped enum constructor native run failed: {err}\n{eval_c}"),
    }
}

#[test]
fn match_with_binding_eval() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := enum\n  | None\n  | Some of (val : int)\n#eval match Some 5 with | None => -1 | Some x => x\n"
            )
            .is_ok()
    );
}

#[test]
fn match_accepts_scoped_constructor_patterns() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := enum\n  | None\n  | Some of (val : int)\n#eval match Option::Some 42 with | Option::None => -1 | Option::Some x => x + 1\n"
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
                "def Option : prop := enum\n  | None\n  | Some of (val : int)\n#eval match None with | None => 0 | Some x => 1\n"
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
            .process_file_str("def Color : prop := enum\n  | Red\n  | Green\n#check Red : int\n")
            .is_err()
    );
}

#[test]
fn wrong_enum_member_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := enum\n  | Red\n  | Green\ndef Shape : prop := enum\n  | Circle\n  | Square\n#check Circle : Color\n"
            )
            .is_err()
    );
}

// ── C codegen ──

#[test]
fn codegen_recursive_enum_typedef() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Nat : prop := enum\n  | Zero\n  | Succ of (pred : Nat)\ndef zero : Nat := Zero\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
    assert!(c.contains("Nat* pred;"), "typedef missing Nat*:\n{c}");
    assert!(c.contains(".Zero = {0}"), "empty variant init wrong:\n{c}");
}

#[test]
fn codegen_recursive_variant_heap_allocates_payload() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Nat : prop := enum\n  | Zero\n  | Succ of (pred : Nat)\ndef one : Nat := Succ Zero\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains(".pred = ({ Nat* _ligare_heap"),
        "recursive field should be heap-backed:\n{c}"
    );
    assert!(
        c.contains("ligare_default_allocate(sizeof(Nat))"),
        "recursive field should use allocator:\n{c}"
    );
    assert!(
        !c.contains("&((Nat)"),
        "recursive field used address-of:\n{c}"
    );
}

// ── Additional match and enum tests (test coverage) ──

#[test]
fn match_nested_variants() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Tree : prop := enum\n  | Leaf\n  | Node of (left : Tree) (val : int) (right : Tree)\ndef t : Tree := Node Leaf 1 Leaf\n#check t : Tree\n"
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
                "def Option : prop := enum\n  | None\n  | Some of (val : int)\n#eval match Some 42 with | None => -1 | Some x => x + 1\n"
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
                "def Color : prop := enum\n  | Red\n  | Green\n  | Blue\ndef f (c : Color) : int := match c with | Red => 1 | Green => 2 | Blue => 3\n"
            )
            .is_ok()
    );
}

#[test]
fn match_single_variant_enum() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Singleton : prop := enum\n  | Only\n#eval match Only with | Only => 99\n"
            )
            .is_ok()
    );
}

#[test]
fn recursive_enum_match() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Nat : prop := enum\n  | Zero\n  | Succ of (pred : Nat)\ndef depth (n : Nat) : int := match n with | Zero => 0 | Succ p => 1 + depth p\n"
            )
            .is_ok()
    );
}

#[test]
fn codegen_recursive_enum_match_compiles_and_runs() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Nat : prop := enum\n  | Zero\n  | Succ of (pred : Nat)\n\
             def depth (n : Nat) : int := match n with | Zero => 0 | Succ p => 1 + depth p\n\
             #eval depth (Succ (Succ Zero))\n",
        )
        .unwrap();
    let eval_c = emit_eval_c(compiler.codegen_input())
        .unwrap_or_else(|e| panic!("{e}"))
        .expect("program has #eval output");
    assert!(
        eval_c.contains("Nat p = *("),
        "recursive match bind should dereference heap payload:\n{eval_c}"
    );
    match compile_and_run_c(&eval_c) {
        Ok(stdout) => assert_eq!(stdout, "2\n"),
        Err(CompileError::CompilerNotFound) => {
            eprintln!("skipping recursive enum native run: C compiler not found")
        }
        Err(err) => panic!("recursive enum native run failed: {err}\n{eval_c}"),
    }
}

#[test]
fn extern_call_clones_recursive_enum_argument() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Nat : prop := enum\n  | Zero\n  | Succ of (pred : Nat)\n\
             extern def smash (n : Nat) : c_int\n\
             def depth (n : Nat) : int := match n with | Zero => 0 | Succ p => 1 + depth p\n\
             def one : Nat := Succ Zero\n\
             #eval unsafe { smash one }\n\
             #eval depth one\n",
        )
        .unwrap();
    let eval_c = emit_eval_c(compiler.codegen_input())
        .unwrap_or_else(|e| panic!("{e}"))
        .expect("program has #eval output");
    assert!(eval_c.contains("ligare_clone_Nat("), "{eval_c}");
    let c_impl = r#"
#include <stdlib.h>
int smash(Nat n) {
    if (n.tag == 1 && n.data.Succ.pred != NULL) {
        Nat* pred = n.data.Succ.pred;
        pred->tag = 1;
        pred->data.Succ.pred = (Nat*)malloc(sizeof(Nat));
        pred->data.Succ.pred->tag = 0;
        pred->data.Succ.pred->data.Zero._empty = 0;
    }
    return 0;
}
"#;
    match compile_and_run_c(&format!("{eval_c}\n{c_impl}")) {
        Ok(stdout) => assert_eq!(stdout, "0\n1\n"),
        Err(CompileError::CompilerNotFound) => {
            eprintln!("skipping extern recursive enum clone test: C compiler not found")
        }
        Err(err) => panic!("extern recursive enum clone test failed: {err}\n{eval_c}"),
    }
}

#[test]
fn enum_with_mixed_payload_types() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Value : prop := enum\n  | IntVal of (n : int)\n  | StrVal of (s : str)\n  | BoolVal of (b : bool)\n#check IntVal 5 : Value\n"
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
                "def Color : prop := enum\n  | Red\n  | Green\n  | Blue\ndef f (c : Color) : int := match c with | Red => 1 | Green => 2\n"
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
            "def Option : prop := enum\n  | None\n  | Some of (val : int)\n#eval match Some 42 with | None => -1 | Some x => x\n",
        )
        .unwrap();
    let c = emit_eval_c(compiler.codegen_input())
        .unwrap_or_else(|e| panic!("{e}"))
        .unwrap();
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
            "def Color : prop := enum\n  | Red\n  | Green\n#eval match Red with | Red => 1 | Green => 2\n#eval match Green with | Red => 10 | Green => 20\n",
        )
        .unwrap();
    let c = emit_eval_c(compiler.codegen_input())
        .unwrap_or_else(|e| panic!("{e}"))
        .unwrap();
    assert!(c.contains("_s0"), "missing _s0:\n{c}");
    assert!(c.contains("_s1"), "missing _s1:\n{c}");
    assert!(c.contains("_r0"), "missing _r0:\n{c}");
    assert!(c.contains("_r1"), "missing _r1:\n{c}");
}

#[test]
fn codegen_function_returning_enum() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Option : prop := enum\n  | None\n  | Some of (val : int)\ndef some_val : Option := Some 42\n#eval some_val\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
    assert!(
        c.contains("const Option some_val"),
        "missing enum const:\n{c}"
    );
    assert!(c.contains("Some"), "missing variant in const:\n{c}");
}

#[test]
fn codegen_tagged_enum_typedef() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "def Shape : prop := enum\n  | Circle\n  | Square\n  | Triangle\ndef s : Shape := Square\ndef c : Shape := Circle\n#eval s\n#eval c\n",
        )
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
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
        .collect_file_str("def Color : prop := enum\n  | Red\n  | Green\ndef x : Color := Red\n")
        .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap_or_else(|e| panic!("{e}"));
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
