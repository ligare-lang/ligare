use bumpalo::Bump;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn compiler() -> Compiler<'static> {
    let bump = Box::leak(Box::new(Bump::new()));
    let arena = Box::leak(Box::new(TermArena::new(bump)));
    Compiler::new(bump, arena)
}

#[test]
fn logic_cannot_reference_unverified_recursive_data_definition() {
    let mut compiler = compiler();
    let err = compiler
        .process_file_str(
            r#"
def loop (x : int) : int := loop x
def Bad := int where (x => loop x == 0)
"#,
        )
        .expect_err("recursive data definition should need a termination proof in logic");

    assert!(
        err.message.contains("without a termination proof: loop"),
        "{err:?}"
    );
}

#[test]
fn logic_can_reference_compiler_proven_terminating_data_definition() {
    let mut compiler = compiler();
    compiler
        .process_file_str(
            r#"
def inc (x : int) : int := x + 1
def Good := int where (x => inc x > 0)
"#,
        )
        .expect("non-recursive data definition should be termination-certified");
}

#[test]
fn terminating_attribute_provides_user_termination_contract() {
    let mut compiler = compiler();
    compiler
        .process_file_str(
            r#"
#[terminating]
def loop (x : int) : int := loop x
def Good := int where (x => loop x == 0)
"#,
        )
        .expect("terminating attribute should allow logical references");
}

#[test]
fn terminating_attribute_accepts_manual_proof() {
    let mut compiler = compiler();
    compiler
        .process_file_str(
            r#"
#[terminating(by exact auto)]
def loop (x : int) : int := loop x
def Good := int where (x => loop x == 0)
"#,
        )
        .expect("manual termination proof should allow logical references");
}

#[test]
fn terminating_attribute_rejects_non_proof_argument() {
    let mut compiler = compiler();
    let err = compiler
        .process_file_str(
            r#"
#[terminating(1)]
def loop (x : int) : int := loop x
"#,
        )
        .expect_err("termination proof argument must be a proof term");

    assert!(
        err.message.contains("termination proof check failed"),
        "{err:?}"
    );
}
