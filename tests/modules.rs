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

fn collect_unlocked(root: &Path) -> Result<Compiler<'static>, ligare::diagnostic::Diagnostic> {
    let bump = Box::leak(Box::new(Bump::new()));
    let arena = Box::leak(Box::new(TermArena::new(bump)));
    let mut compiler = Compiler::new(bump, arena);
    compiler.collect_file(&root.join("main.lig").to_string_lossy())?;
    Ok(compiler)
}

fn collect(root: &Path) -> Result<Compiler<'static>, ligare::diagnostic::Diagnostic> {
    let _guard = env_lock().lock().unwrap();
    collect_unlocked(root)
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
    let c = emit_c(compiler.codegen_input()).unwrap();
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
    let compiler = with_ligare_std_path(None, || {
        let bump = Box::leak(Box::new(Bump::new()));
        let arena = Box::leak(Box::new(TermArena::new(bump)));
        let mut compiler = Compiler::new(bump, arena);
        compiler
            .collect_file(&root.join("test.lig").to_string_lossy())
            .unwrap();
        compiler
    });

    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "main")
    }));
    let c = emit_c(compiler.codegen_input()).unwrap();
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
fn wildcard_imports_public_symbols_from_module() {
    let root = temp_project();
    write(
        &root,
        "math.lig",
        "pub def one : int := 1\npub def inc (x : int) : int := x + 1\ndef hidden : int := 0\n",
    );
    write(
        &root,
        "main.lig",
        "mod math\nuse math::*\npub def main : IO () := let _ := inc one in ()\n",
    );

    collect(&root).unwrap();
}

#[test]
fn wildcard_import_resolves_relative_child_module() {
    let root = temp_project();
    write(&root, "ops/mod.lig", "pub use convert::*\nmod convert\n");
    write(
        &root,
        "ops/convert.lig",
        "pub def eq (x : int) : bool := true\n",
    );
    write(
        &root,
        "main.lig",
        "mod ops\nuse ops::*\npub def main : IO () := let _ := eq 1 in ()\n",
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
fn qualified_module_call_without_use_resolves_public_symbol() {
    let root = temp_project();
    write(&root, "math.lig", "pub def one : int := 1\n");
    write(
        &root,
        "main.lig",
        "mod math\npub def main : IO () := let _ := math::one in ()\n",
    );

    let compiler = collect(&root).unwrap();

    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "math::one")
    }));
}

#[test]
fn namespace_use_forms_resolve_public_functions() {
    let root = temp_project();
    write(
        &root,
        "math.lig",
        r#"
namespace Ops {
  pub def inc (x : int) : int := x + 1
  pub def dec (x : int) : int := x - 1
  def hidden (x : int) : int := x
}
"#,
    );
    write(
        &root,
        "main.lig",
        r#"
mod math
use math::Ops::inc
use math::Ops
use math::Ops::*
pub def main : IO () := let _ := inc 1 in let _ := Ops::dec 3 in let _ := dec 4 in ()
"#,
    );

    let compiler = collect(&root).unwrap();

    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "math::Ops::inc")
    }));
}

#[test]
fn namespace_private_item_cannot_be_imported() {
    let root = temp_project();
    write(
        &root,
        "math.lig",
        "namespace Ops { def hidden (x : int) : int := x }\n",
    );
    write(
        &root,
        "main.lig",
        "mod math\nuse math::Ops::hidden\npub def main : IO () := hidden 1\n",
    );

    assert_module_error(&root, "private or unknown symbol");
}

#[test]
fn namespace_conflicting_function_arity_is_rejected() {
    let root = temp_project();
    write(
        &root,
        "math.lig",
        r#"
namespace Ops { pub def same (x : int) : int := x }
namespace Ops { pub def same (y : int) : int := y }
"#,
    );
    write(
        &root,
        "main.lig",
        "mod math\nuse math::Ops::same\npub def main : IO () := same 1\n",
    );

    assert_module_error(&root, "conflicting function `same`");
}

#[test]
fn namespace_imports_with_same_name_merge_across_modules() {
    let root = temp_project();
    write(
        &root,
        "a.lig",
        "namespace Ops { pub def inc (x : int) : int := x + 1 }\n",
    );
    write(
        &root,
        "b.lig",
        "namespace Ops { pub def dec (x : int) : int := x - 1 }\n",
    );
    write(
        &root,
        "main.lig",
        r#"
mod a
mod b
use a::Ops
use b::Ops
pub def main : IO () := let _ := Ops::inc 1 in let _ := Ops::dec 2 in ()
"#,
    );

    collect(&root).unwrap();
}

#[test]
fn qualified_module_call_without_use_rejects_private_symbol() {
    let root = temp_project();
    write(&root, "math.lig", "def hidden : int := 1\n");
    write(
        &root,
        "main.lig",
        "mod math\npub def main : IO () := let _ := math::hidden in ()\n",
    );

    assert_module_error(&root, "private or unknown symbol");
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
        collect_unlocked(&root)
    })
    .unwrap();

    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "std::answer::value")
    }));
}

#[test]
fn std_prelude_is_implicitly_imported_for_root_modules() {
    let root = temp_project();
    let std_root = root.join("custom_std");
    write_std(&std_root, "lib.lig", "pub mod prelude\npub mod answer\n");
    write_std(&std_root, "prelude.lig", "pub use std::answer::value\n");
    write_std(&std_root, "answer.lig", "pub def value : int := 41 + 1\n");
    write(&root, "helper.lig", "pub def run : int := value\n");
    write(
        &root,
        "main.lig",
        "mod helper\nuse helper::run\npub def main : IO () := let _ := value in let _ := run in ()\n",
    );

    with_ligare_std_path(Some(std_root.to_string_lossy().into_owned()), || {
        collect_unlocked(&root)
    })
    .unwrap();
}

#[test]
fn std_package_modules_do_not_implicitly_import_prelude() {
    let root = temp_project();
    let std_root = root.join("custom_std");
    write_std(&std_root, "lib.lig", "pub mod prelude\npub mod primitive\n");
    write_std(&std_root, "prelude.lig", "pub use std::primitive::*\n");
    write_std(&std_root, "primitive.lig", "pub def value : int := 1\n");
    write(
        &root,
        "main.lig",
        "pub def main : IO () := let _ := value in ()\n",
    );

    with_ligare_std_path(Some(std_root.to_string_lossy().into_owned()), || {
        collect_unlocked(&root)
    })
    .unwrap();
}

#[test]
fn std_prelude_primitives_are_compiler_intrinsics() {
    let root = temp_project();
    write(
        &root,
        "main.lig",
        "use std::prelude::*\n\
         extern def puts (s : str) : IO c_int\n\
         pub def main : IO () := do\n\
           let n : int = 5\n\
           let _ = unsafe { puts \"hello\" }\n\
           ()\n",
    );

    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("libs/std");
    let compiler = with_ligare_std_path(Some(std_root.to_string_lossy().into_owned()), || {
        collect_unlocked(&root)
    })
    .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap();

    assert!(c.contains("extern int puts(const char*);"), "{c}");
    assert!(!c.contains("std_primitive_int"), "{c}");
}

#[test]
fn real_std_vec_import_checks() {
    let root = temp_project();
    write(
        &root,
        "main.lig",
        "use std::mem::vec::Vec\n\
         use std::data::nat::Zero\n\
         use std::data::nat::Succ\n\
         pub def main : IO () := do\n\
           let empty : Vec int Zero = Nil\n\
           let one : Vec int (Succ Zero) = Cons 1 empty\n\
           ()\n",
    );

    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("libs/std");
    with_ligare_std_path(Some(std_root.to_string_lossy().into_owned()), || {
        collect_unlocked(&root)
    })
    .unwrap();
}

#[test]
fn real_std_vec_codegen_uses_layout_type_only() {
    let root = temp_project();
    write(
        &root,
        "main.lig",
        "use std::mem::vec::Vec\n\
         use std::data::nat::Zero\n\
         pub def main : IO () := do\n\
           let vec : Vec int Zero = Nil\n\
           let vec_1 = vec.append 1\n\
           ()\n",
    );

    let std_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("libs/std");
    let compiler = with_ligare_std_path(Some(std_root.to_string_lossy().into_owned()), || {
        collect_unlocked(&root)
    })
    .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap();

    assert!(c.contains("std__mem__vec__Vec__int"), "{c}");
    assert!(!c.contains("std__mem__vec__Vec__int__n0"), "{c}");
    assert!(!c.contains("std__mem__vec__Vec__int__n1"), "{c}");
}

#[test]
fn qualified_std_call_without_use_resolves_public_symbol() {
    let root = temp_project();
    let std_root = root.join("custom_std");
    write_std(&std_root, "lib.lig", "pub mod io\n");
    write_std(
        &std_root,
        "io.lig",
        "extern def puts (s : str) : IO c_int\n\
         pub def put_str (s : str) : IO () := do\n\
           let _ = unsafe { puts s }\n\
           ()\n",
    );
    write(
        &root,
        "main.lig",
        "pub def main : IO () := do\n\
           let _ = std::io::put_str \"hello\"\n\
           ()\n",
    );

    let compiler = with_ligare_std_path(Some(std_root.to_string_lossy().into_owned()), || {
        collect_unlocked(&root)
    })
    .unwrap();

    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "std::io::put_str")
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

    let err = match with_ligare_std_path(None, || collect_unlocked(&root)) {
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
        collect_unlocked(&root)
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
        collect_unlocked(&root)
    })
    .unwrap();
    let c = emit_c(compiler.codegen_input()).unwrap();

    assert!(c.contains("const int64_t std_answer_value = 1;"), "{c}");
    assert!(!c.contains("const int64_t std_answer_value = 2;"), "{c}");
}
