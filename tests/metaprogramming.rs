use ligare::backend::c::emit_eval_c;
use ligare::backend::compile::compile_and_run_c;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn compiler<'bump>(bump: &'bump bumpalo::Bump, arena: &'bump TermArena<'bump>) -> Compiler<'bump> {
    Compiler::new(bump, arena)
}

#[test]
fn quote_checks_as_expr() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .process_file_str("#check quote { 1 + 2 } : Expr\n")
        .unwrap();
}

#[test]
fn splice_inserts_code_and_eval_runs() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .collect_file_str("#eval $(quote { 1 + 2 })\n")
        .unwrap();
    let c = emit_eval_c(compiler.codegen_input()).unwrap().unwrap();
    let stdout = compile_and_run_c(&c).unwrap();
    assert_eq!(stdout, "3\n");
}

#[test]
fn nested_quote_splice_eval_runs() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .collect_file_str("#eval $(quote { 1 + $(quote { 2 }) })\n")
        .unwrap();
    let c = emit_eval_c(compiler.codegen_input()).unwrap().unwrap();
    let stdout = compile_and_run_c(&c).unwrap();
    assert_eq!(stdout, "3\n");
}

#[test]
fn splice_rejects_non_expr() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    let err = compiler
        .process_file_str("def bad : int := $(1)\n")
        .expect_err("splice should require Expr");
    assert!(
        err.message
            .contains("splice expression must have type Expr")
    );
}

#[test]
fn splice_result_is_constraint_checked() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    let err = compiler
        .process_file_str("def bad : bool := $(quote { 1 })\n")
        .expect_err("inserted term should still be checked");
    assert!(err.message.contains("definition bad failed"), "{err:?}");
}

#[test]
fn top_level_splice_generates_definition_and_eval_runs() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .collect_file_str(
            r#"
def generated_defs : Definitions :=
  Cons (Def "answer" (Name "int") (Int 41)) (Cons (Def "inc" (Pi "x" (Name "int") (Name "int")) (Lam (App (App (Prim "+") (Var 0)) (Int 1)))) Nil)
$(generated_defs)
#eval inc answer
"#,
        )
        .unwrap();
    let c = emit_eval_c(compiler.codegen_input()).unwrap().unwrap();
    let stdout = compile_and_run_c(&c).unwrap();
    assert_eq!(stdout, "42\n");
}

#[test]
fn top_level_splice_generates_instance() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .process_file_str(
            r#"
def ShowInt : prop := struct
  show : int -> str

def show_int (x : int) : str := "int"
def generated_instances : Definitions :=
  Cons (Instance "showGenerated" (Name "ShowInt") (App (Global "ShowInt.mk") (Global "show_int"))) Nil
$(generated_instances)

def render {s : ShowInt} (x : int) : str := ShowInt.show s x
#check render 1 : str
"#,
        )
        .unwrap();
}

#[test]
fn derive_attribute_generates_definition() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .collect_file_str(
            r#"
def derive_Answer (item : Expr) : Definitions :=
  Cons (Def "answer_from_derive" (Name "int") (Int 7)) Nil

#[derive(Answer)]
def Marker : prop := struct
  value : int

#eval answer_from_derive + 1
"#,
        )
        .unwrap();
    let c = emit_eval_c(compiler.codegen_input()).unwrap().unwrap();
    let stdout = compile_and_run_c(&c).unwrap();
    assert_eq!(stdout, "8\n");
}

#[test]
fn stacked_and_parameterized_attributes_generate_in_order() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .collect_file_str(
            r#"
#[attr]
def first_attr (item : Expr) : Definitions :=
  Cons (Def "first_value" (Name "int") (Int 10)) Nil
#[attr]
def repr (item : Expr) (tag : Expr) : Definitions :=
  Cons (Def "repr_value" (Name "int") (Int 32)) Nil

#[first_attr]
#[repr(C)]
def Host : int := 0

#eval first_value + repr_value
"#,
        )
        .unwrap();
    let c = emit_eval_c(compiler.codegen_input()).unwrap().unwrap();
    let stdout = compile_and_run_c(&c).unwrap();
    assert_eq!(stdout, "42\n");
}

#[test]
fn top_level_splice_rejects_non_definitions() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    let err = compiler
        .process_file_str("$(quote { 1 })\n")
        .expect_err("top-level splice should require Definitions");
    assert!(
        err.message.contains("must have type Definitions"),
        "{err:?}"
    );
}

#[test]
fn tactic_attribute_registers_and_by_call_generates_proof() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .process_file_str(
            r#"
#[tactic]
def make_int (goal : Expr) : Expr := Int 42

theorem answer : int := by make_int()
#check answer : int
"#,
        )
        .unwrap();
}

#[test]
fn tactic_signature_error_rejects_registration() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    let err = compiler
        .process_file_str(
            r#"
#[tactic]
def bad_tactic (goal : int) : Expr := Int 0
"#,
        )
        .expect_err("bad tactic signature should fail");
    assert!(
        err.message
            .contains("cannot be used as tactic: first parameter must be Expr"),
        "{err:?}"
    );
}

#[test]
fn tactic_extra_expr_argument_is_quoted_and_passed() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .process_file_str(
            r#"
def proof_expr (n : int) : Expr := Int n

#[tactic]
def exact_expr (goal : Expr) (n : int) : Expr := proof_expr n

theorem answer : int := by exact_expr(42)
#check answer : int
"#,
        )
        .unwrap();
}

#[test]
fn by_missing_tactic_marker_reports_clear_error() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    let err = compiler
        .process_file_str(
            r#"
def plain_tactic (goal : Expr) : Expr := Int 1
theorem answer : int := by plain_tactic()
"#,
        )
        .expect_err("unmarked tactic should fail");
    assert!(
        err.message
            .contains("not a valid tactic (missing #[tactic] marker)"),
        "{err:?}"
    );
}

#[test]
fn attr_attribute_registers_and_generates_definition() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    compiler
        .collect_file_str(
            r#"
#[attr]
def make_answer (item : Expr) : Definitions :=
  Cons (Def "answer_from_attr" (Name "int") (Int 42)) Nil

#[make_answer]
def Host : int := 0

#eval answer_from_attr
"#,
        )
        .unwrap();
    let c = emit_eval_c(compiler.codegen_input()).unwrap().unwrap();
    let stdout = compile_and_run_c(&c).unwrap();
    assert_eq!(stdout, "42\n");
}

#[test]
fn attr_signature_error_rejects_registration() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    let err = compiler
        .process_file_str(
            r#"
#[attr]
def bad_attr (item : Expr) : Expr := item
"#,
        )
        .expect_err("bad attribute signature should fail");
    assert!(
        err.message
            .contains("cannot be used as attr: return value must be Definitions"),
        "{err:?}"
    );
}

#[test]
fn custom_attribute_missing_marker_reports_clear_error() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    let err = compiler
        .process_file_str(
            r#"
def plain_attr (item : Expr) : Definitions := Nil

#[plain_attr]
def Host : int := 0
"#,
        )
        .expect_err("unmarked attribute should fail");
    assert!(
        err.message
            .contains("not a valid attribute (missing #[attr] marker)"),
        "{err:?}"
    );
}

#[test]
fn generated_top_level_definition_is_constraint_checked() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = compiler(&bump, &arena);
    let err = compiler
        .process_file_str(
            r#"
def generated_defs : Definitions :=
  Cons (Def "bad_generated" (Name "bool") (Int 1)) Nil
$(generated_defs)
"#,
        )
        .expect_err("generated definition should be checked");
    assert!(
        err.message.contains("definition bad_generated failed"),
        "{err:?}"
    );
}
