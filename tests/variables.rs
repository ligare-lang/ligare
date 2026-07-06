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
fn variable_adds_current_scope_implicit_type_parameter() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
variable {A : prop}
def id (x : A) : A := x
#check id 1 : int
"#,
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn variable_adds_current_scope_implicit_instance_parameter() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(
        r#"
def ShowInt : prop := struct
  show : int -> str

def show_int (x : int) : str := "int"
variable {s : ShowInt}
def render (x : int) : str := ShowInt.show s x
instance showInt : ShowInt := ShowInt.mk show_int
#check render 1 : str
"#,
    );
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn variable_scoped_implicit_params_are_collected_for_codegen() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    compiler
        .collect_file_str(
            r#"
variable {A : prop}
def id (x : A) : A := x
def main : int := id 1
"#,
        )
        .expect("program should collect");
    let input = compiler.codegen_input();
    let c = emit_c(input).expect("C generation should succeed");
    assert!(c.contains("main"), "{c}");
}
