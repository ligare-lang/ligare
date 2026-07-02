use bumpalo::Bump;
use ligare::backend::c::emit_c;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn temp_project() -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "ligare_modules_{}_{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn env_lock() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

fn write(root: &Path, rel: &str, content: &str) {
    let path = root.join(rel);
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(path, content).unwrap();
}

fn write_std(root: &Path, rel: &str, content: &str) {
    write(root, &format!("src/{rel}"), content);
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

fn with_ligare_std_path<T>(value: Option<String>, f: impl FnOnce() -> T) -> T {
    let _guard = env_lock().lock().unwrap();
    let old = std::env::var_os("LIGARE_STD_PATH");
    unsafe {
        match value {
            Some(value) => std::env::set_var("LIGARE_STD_PATH", value),
            None => std::env::remove_var("LIGARE_STD_PATH"),
        }
    }
    let result = f();
    unsafe {
        match old {
            Some(old) => std::env::set_var("LIGARE_STD_PATH", old),
            None => std::env::remove_var("LIGARE_STD_PATH"),
        }
    }
    result
}

#[test]
fn single_level_import_codegen_uses_prefixed_c_name() {
    let root = temp_project();
    write(
        &root,
        "nat.lig",
        "pub def add (a : int) (b : int) : int := a + b\n",
    );
    write(
        &root,
        "main.lig",
        "mod nat\nuse nat::add\npub def main : IO () := let _ := add 2 3 in ()\n",
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
    write(&root, "data/mod.lig", "pub mod nat\n");
    write(
        &root,
        "data/nat.lig",
        "pub def add (a : int) (b : int) : int := a + b\npub def one : int := 1\n",
    );
    write(
        &root,
        "main.lig",
        "mod data\nuse data::nat::{add as plus, one}\npub def main : IO () := let _ := plus one 2 in ()\n",
    );
    let compiler = collect(&root).unwrap();
    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "data::nat::add")
    }));
}

#[test]
fn non_main_file_with_import_uses_module_pipeline() {
    let root = temp_project();
    write(
        &root,
        "libs/std/lib.lig",
        "extern def puts (s : str) : IO c_int\n\
         pub def put_str (s : str) : IO () := do\n\
           let _ = unsafe { puts s }\n\
           ()\n",
    );
    write(
        &root,
        "test.lig",
        "mod libs\n\
         use libs::std::lib::put_str\n\
         pub def main : IO () := do\n\
           let _ = put_str \"hello world\"\n\
           ()\n",
    );
    write(&root, "libs/mod.lig", "pub mod std\n");
    write(&root, "libs/std/mod.lig", "pub mod lib\n");
    let bump = Box::leak(Box::new(Bump::new()));
    let arena = Box::leak(Box::new(TermArena::new(bump)));
    let mut compiler = Compiler::new(bump, arena);
    compiler
        .collect_file(&root.join("test.lig").to_string_lossy())
        .unwrap();

    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "main")
    }));
    let c = emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap();
    assert!(c.contains("extern int puts(const char*);"), "{c}");
    assert!(!c.contains("libs_std_lib_puts"), "{c}");
}

#[test]
fn private_access_is_rejected() {
    let root = temp_project();
    write(&root, "data/mod.lig", "pub mod nat\n");
    write(&root, "data/nat.lig", "def hidden : int := 1\n");
    write(
        &root,
        "main.lig",
        "mod data\nuse data::nat::hidden\npub def main : IO () := hidden\n",
    );
    assert_module_error(&root, "private or unknown symbol");
}

#[test]
fn re_export_allows_import_from_facade() {
    let root = temp_project();
    write(
        &root,
        "data/nat.lig",
        "pub def add (a : int) (b : int) : int := a + b\n",
    );
    write(&root, "data/mod.lig", "pub mod nat\n");
    write(&root, "prelude.lig", "pub use data::nat::add\n");
    write(
        &root,
        "main.lig",
        "mod data\nmod prelude\nuse prelude::add\npub def main : IO () := let _ := add 1 2 in ()\n",
    );
    collect(&root).unwrap();
}

#[test]
fn cycle_dependency_reports_error() {
    let root = temp_project();
    write(&root, "a.lig", "mod b\nuse a::b::y\npub def x : int := y\n");
    write(&root, "a/b.lig", "use a::x\npub def y : int := x\n");
    write(
        &root,
        "main.lig",
        "mod a\nuse a::x\npub def main : IO () := x\n",
    );
    assert_module_error(&root, "cyclic module dependency");
}

#[test]
fn missing_module_reports_error() {
    let root = temp_project();
    write(
        &root,
        "main.lig",
        "use nope::x\npub def main : IO () := x\n",
    );
    assert_module_error(&root, "not declared by parent module");
}

#[test]
fn entry_requires_public_main() {
    let root = temp_project();
    write(&root, "main.lig", "def main : IO () := 0\n");
    assert_module_error(&root, "must define `pub main");
}

#[test]
fn folder_module_uses_mod_lig() {
    let root = temp_project();
    write(&root, "math/mod.lig", "pub def one : int := 1\n");
    write(
        &root,
        "main.lig",
        "mod math\nuse math::one\npub def main : IO () := let _ := one in ()\n",
    );
    let compiler = collect(&root).unwrap();
    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "math::one")
    }));
}

#[test]
fn imported_module_must_be_declared_by_parent() {
    let root = temp_project();
    write(&root, "math.lig", "pub def one : int := 1\n");
    write(
        &root,
        "main.lig",
        "use math::one\npub def main : IO () := let _ := one in ()\n",
    );
    assert_module_error(&root, "not declared by parent module");
}

#[test]
fn std_import_uses_ligare_std_path() {
    let root = temp_project();
    let std_root = root.join("custom_std");
    write_std(&std_root, "lib.lig", "pub mod answer\n");
    write_std(&std_root, "answer.lig", "pub def value : int := 41 + 1\n");
    write(
        &root,
        "main.lig",
        "use std::answer::value\npub def main : IO () := let _ := value in ()\n",
    );

    let compiler = with_ligare_std_path(Some(std_root.to_string_lossy().into_owned()), || {
        collect(&root)
    })
    .unwrap();

    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "std::answer::value")
    }));
}

#[test]
fn std_import_reports_default_path_when_env_is_unset() {
    let root = temp_project();
    write(
        &root,
        "main.lig",
        "use std::missing::value\npub def main : IO () := value\n",
    );

    let err = match with_ligare_std_path(None, || collect(&root)) {
        Ok(_) => panic!("expected missing standard library module to fail"),
        Err(err) => err,
    };
    assert!(
        err.message
            .contains("standard library module `std::missing` not found"),
        "{}",
        err.message
    );
    assert!(
        err.message.contains("/usr/lib/ligare/std"),
        "{}",
        err.message
    );
    assert!(err.message.contains("tried:"), "{}", err.message);
}

#[test]
fn missing_std_module_lists_all_attempted_search_paths() {
    let root = temp_project();
    let first = root.join("first_std");
    let second = root.join("second_std");
    write_std(&first, "lib.lig", "pub mod missing\n");
    write_std(&second, "lib.lig", "pub mod missing\n");
    write(
        &root,
        "main.lig",
        "use std::missing::value\npub def main : IO () := value\n",
    );
    let joined = std::env::join_paths([first.clone(), second.clone()]).unwrap();

    let err = match with_ligare_std_path(Some(joined.to_string_lossy().into_owned()), || {
        collect(&root)
    }) {
        Ok(_) => panic!("expected missing standard library module to fail"),
        Err(err) => err,
    };

    assert!(
        err.message
            .contains("standard library module `std::missing` not found"),
        "{}",
        err.message
    );
    assert!(
        err.message
            .contains(&first.join("src/missing.lig").display().to_string()),
        "{}",
        err.message
    );
    assert!(
        err.message
            .contains(&second.join("src/missing.lig").display().to_string()),
        "{}",
        err.message
    );
}

#[test]
fn std_path_searches_multiple_roots_in_order() {
    let root = temp_project();
    let first = root.join("first_std");
    let second = root.join("second_std");
    write_std(&first, "lib.lig", "pub mod answer\n");
    write_std(&first, "answer.lig", "pub def value : int := 1\n");
    write_std(&second, "lib.lig", "pub mod answer\n");
    write_std(&second, "answer.lig", "pub def value : int := 2\n");
    write(
        &root,
        "main.lig",
        "use std::answer::value\npub def main : IO () := let _ := value in ()\n",
    );
    let joined = std::env::join_paths([first, second]).unwrap();

    let compiler = with_ligare_std_path(Some(joined.to_string_lossy().into_owned()), || {
        collect(&root)
    })
    .unwrap();
    let c = emit_c(
        compiler.tops(),
        compiler.raw_defs(),
        compiler.fun_sigs(),
        &compiler.union_types,
        &compiler.struct_types,
    )
    .unwrap();

    assert!(c.contains("const int64_t std_answer_value = 1;"), "{c}");
    assert!(!c.contains("const int64_t std_answer_value = 2;"), "{c}");
}
