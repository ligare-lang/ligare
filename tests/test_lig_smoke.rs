//! End-to-end coverage for the top-level examples mirrored from `test.lig`.

use bumpalo::Bump;
use ligare::backend::c::{emit_c, emit_eval_c};
use ligare::backend::compile::{CompileError, compile_and_run_c};
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    (b, TermArena::new(b))
}

fn process_ok(source: &str) {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(source);
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn test_lig_fixture_runs_end_to_end() {
    process_ok(include_str!("fixtures/test.lig"));
}

#[test]
fn ffi_fixture_compiles_and_runs_with_expected_output() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file("tests/fixtures/ffi.lig")
        .expect("ffi fixture should pass compile pipeline collection");
    let codegen = compiler.codegen_input();
    let generated = emit_c(codegen).expect("ffi fixture should emit C");
    assert!(
        generated.contains("extern int64_t ffi_abs(int64_t);"),
        "missing ffi_abs prototype:\n{generated}"
    );
    assert!(
        generated.contains("extern int64_t ffi_read();"),
        "missing ffi_read prototype:\n{generated}"
    );
    assert!(
        generated.contains("ffi_abs("),
        "missing direct ffi_abs call"
    );
    assert!(
        generated.contains("ffi_read()"),
        "missing direct ffi_read call"
    );
    assert!(
        !generated.contains("int64_t ffi_abs(int64_t) {"),
        "extern should not generate wrapper definition:\n{generated}"
    );
    let eval_c = emit_eval_c(codegen)
        .expect("ffi fixture should emit eval C")
        .expect("ffi fixture has #eval outputs");

    let c_impl = "#include <stdint.h>\nint64_t ffi_abs(int64_t x) { return x < 0 ? -x : x; }\nint64_t ffi_read() { return 42; }\n";
    match compile_and_run_c(&format!("{c_impl}\n{eval_c}")) {
        Ok(stdout) => assert_eq!(stdout, "7\n8\n"),
        Err(CompileError::CompilerNotFound) => {
            eprintln!("skipping native FFI fixture run: C compiler not found")
        }
        Err(err) => panic!("native FFI fixture run failed: {err}"),
    }
}

#[test]
fn bare_top_level_expression_prints_from_generated_executable() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str("\"hello world\"\n")
        .expect("bare expression should pass compile pipeline collection");
    let codegen = compiler.codegen_input();
    let generated = emit_c(codegen).expect("bare expression should emit final C");
    assert!(generated.contains("printf(\"%s\\n\""), "{generated}");
    match compile_and_run_c(&generated) {
        Ok(stdout) => assert_eq!(stdout, "hello world\n"),
        Err(CompileError::CompilerNotFound) => {
            eprintln!("skipping native runtime output test: C compiler not found")
        }
        Err(err) => panic!("native runtime output test failed: {err}"),
    }
}

#[test]
fn ffi_puts_main_prints_from_generated_executable() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            "extern def puts (s : str) : IO c_int\n\
             def main : IO c_int := unsafe { puts \"hello world\" }\n",
        )
        .expect("puts main should pass compile pipeline collection");
    let codegen = compiler.codegen_input();
    let generated = emit_c(codegen).expect("puts main should emit final C");
    assert!(
        generated.contains("extern int puts(const char*);"),
        "{generated}"
    );
    assert!(
        !generated.contains("const int main"),
        "Ligare main must not be emitted as a global const:\n{generated}"
    );
    match compile_and_run_c(&generated) {
        Ok(stdout) => assert_eq!(stdout, "hello world\n"),
        Err(CompileError::CompilerNotFound) => {
            eprintln!("skipping native puts main test: C compiler not found")
        }
        Err(err) => panic!("native puts main test failed: {err}\nC:\n{generated}"),
    }
}

#[test]
fn sdiv_refinement_parameter_checks_from_source() {
    process_ok(
        "def sdiv (a : int) (b : int where (x => x /= 0)) := a / b\n\
         #check sdiv 1 1 : int\n",
    );
}

#[test]
fn theorem_names_remain_available_to_later_terms() {
    process_ok(
        "def Nat := int where (x => x >= 0)\n\
         theorem zero_is_nat : Nat := 0 by\n  exact true\n\
         theorem identity : int -> int := fun x => x\n\
         #check zero_is_nat : Nat\n\
         #check identity 5 : int\n",
    );
}

#[test]
fn theorem_with_fun_syntax_checks_from_source() {
    process_ok(
        "theorem add_one : int -> int := fun x => x + 1\n\
         #check add_one 5 : int\n",
    );
}

#[test]
fn top_level_string_definition_application_and_show() {
    process_ok(
        "def some_sth : str := \"hello\"\n\
         def some_fn (s : str) := s\n\
         #check some_fn some_sth : str\n\
         #check \"hello\" : data\n\
         #eval some_fn some_sth\n",
    );
}
