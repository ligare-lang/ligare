use bumpalo::Bump;
use ligare::backend::c::{CEmitOptions, CTarget, emit_c, emit_c_with_options};
use ligare::backend::compile::compile_and_run_c;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let bump = Box::leak(Box::new(Bump::new()));
    (bump, TermArena::new(bump))
}

fn emit(source: &str) -> String {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(source)
        .expect("program should collect");
    let input = compiler.codegen_input();
    emit_c(
        input.tops,
        input.raw_defs,
        input.fun_sigs,
        input.enum_types,
        input.struct_types,
    )
    .expect("C generation should succeed")
}

#[test]
fn default_global_allocator_supports_string_concat() {
    let c = emit(r#"def main : str := "hel" + "lo""#);
    assert!(c.contains("ligare_default_allocate"), "{c}");
    assert!(c.contains("malloc(size)"), "{c}");
    assert!(
        c.contains("ligare_default_allocate(_ligare_ln0 + _ligare_rn0 + 1)"),
        "{c}"
    );
    let output = compile_and_run_c(&c).expect("generated C should compile and run");
    assert_eq!(output, "");
}

#[test]
fn custom_global_allocator_overrides_default() {
    let c = emit(
        r#"
def Allocator : prop := struct
  allocate : int -> ptr c_int
  deallocate : ptr c_int -> int
  reallocate : ptr c_int -> int -> ptr c_int

extern def tracked_alloc (n : int) : ptr c_int
extern def tracked_dealloc (p : ptr c_int) : int
extern def tracked_realloc (p : ptr c_int) (n : int) : ptr c_int

#[global_allocator]
def alloc : Allocator := Allocator.mk tracked_alloc tracked_dealloc tracked_realloc

def main : str := "a" + "b"
"#,
    );
    assert!(
        c.contains("tracked_alloc(_ligare_ln0 + _ligare_rn0 + 1)"),
        "{c}"
    );
    assert!(c.contains("extern int* tracked_alloc"), "{c}");
    assert!(!c.contains("ligare_default_allocate"), "{c}");
    assert!(!c.contains("malloc(size)"), "{c}");
}

#[test]
fn bare_metal_target_requires_explicit_allocator_for_implicit_allocation() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(r#"def main : str := "a" + "b""#)
        .expect("program should collect");
    let input = compiler.codegen_input();
    let err = emit_c_with_options(
        input.tops,
        input.raw_defs,
        input.fun_sigs,
        input.enum_types,
        input.struct_types,
        CEmitOptions {
            target: CTarget::BareMetal,
        },
    )
    .expect_err("bare-metal target should require a global allocator");
    assert!(err.message.contains("bare-metal target"), "{}", err.message);
    assert!(
        err.message.contains("#[global_allocator]"),
        "{}",
        err.message
    );
}

#[test]
fn generated_c_expands_string_concat_to_direct_allocator_call() {
    let c = emit(r#"def joined : str := "a" + "b""#);
    assert!(c.contains("const char* joined(void) {"), "{c}");
    assert!(
        c.contains("char* _ligare_out0 = (char*)ligare_default_allocate"),
        "{c}"
    );
    assert!(!c.contains("ligare_str_concat"), "{c}");
    let output = compile_and_run_c(&c).expect("generated C should compile and run");
    assert_eq!(output, "");
}
