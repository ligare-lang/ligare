use bumpalo::Bump;
use ligare::backend::c::emit_c;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn temp_project() -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "ligare_modules_{}_{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(root: &Path, rel: &str, content: &str) {
    let path = root.join(rel);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, content).unwrap();
}

fn collect(root: &Path) -> Result<Compiler<'static>, ligare::diagnostic::Diagnostic> {
    let bump = Box::leak(Box::new(Bump::new()));
    let arena = Box::leak(Box::new(TermArena::new(bump)));
    let mut compiler = Compiler::new(bump, arena);
    compiler.collect_file(&root.join("main.lig").to_string_lossy())?;
    Ok(compiler)
}

fn assert_module_error(root: &Path, needle: &str) {
    let err = match collect(root) {
        Ok(_) => panic!("expected module error containing `{needle}`"),
        Err(err) => err,
    };
    assert!(
        err.message.contains(needle),
        "expected error containing `{needle}`, got `{}`",
        err.message
    );
}

#[test]
fn single_level_import_codegen_uses_prefixed_c_name() {
    let root = temp_project();
    write(&root, "nat.lig", "pub def add (a : int) (b : int) : int := a + b\n");
    write(
        &root,
        "main.lig",
        "use nat::add\npub def main : IO Unit := let _ := add 2 3 in Unit\n",
    );
    let compiler = collect(&root).unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap();
    assert!(c.contains("nat_add"), "{c}");
}

#[test]
fn nested_batch_import_and_alias() {
    let root = temp_project();
    write(
        &root,
        "data/nat.lig",
        "pub def add (a : int) (b : int) : int := a + b\npub def one : int := 1\n",
    );
    write(
        &root,
        "main.lig",
        "use data::nat::{add as plus, one}\npub def main : IO Unit := let _ := plus one 2 in Unit\n",
    );
    let compiler = collect(&root).unwrap();
    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "data::nat::add")
    }));
}

#[test]
fn private_access_is_rejected() {
    let root = temp_project();
    write(&root, "data/nat.lig", "def hidden : int := 1\n");
    write(&root, "main.lig", "use data::nat::hidden\npub def main : IO Unit := hidden\n");
    assert_module_error(&root, "private or unknown symbol");
}

#[test]
fn re_export_allows_import_from_facade() {
    let root = temp_project();
    write(&root, "data/nat.lig", "pub def add (a : int) (b : int) : int := a + b\n");
    write(&root, "prelude.lig", "pub use data::nat::add\n");
    write(&root, "main.lig", "use prelude::add\npub def main : IO Unit := let _ := add 1 2 in Unit\n");
    collect(&root).unwrap();
}

#[test]
fn cycle_dependency_reports_error() {
    let root = temp_project();
    write(&root, "a.lig", "use b::y\npub def x : int := y\n");
    write(&root, "b.lig", "use a::x\npub def y : int := x\n");
    write(&root, "main.lig", "use a::x\npub def main : IO Unit := x\n");
    assert_module_error(&root, "cyclic module dependency");
}

#[test]
fn missing_module_reports_error() {
    let root = temp_project();
    write(&root, "main.lig", "use nope::x\npub def main : IO Unit := x\n");
    assert_module_error(&root, "module not found");
}

#[test]
fn entry_requires_public_main() {
    let root = temp_project();
    write(&root, "main.lig", "def main : IO Unit := 0\n");
    assert_module_error(&root, "must define `pub main");
}
