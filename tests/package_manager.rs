use bumpalo::Bump;
use ligare::compiler::Compiler;
use ligare::compiler::cache::{PackageCompilerCache, cache_file_path, source_hash};
use ligare::core::pool::TermArena;
use ligare::package::{PackageType, UpdateMode, resolve_project, write_lock};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn temp_project() -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "ligare_packages_{}_{}_{}",
        std::process::id(),
        nanos,
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
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

fn manifest(root: &Path, name: &str, body: &str) {
    write(
        root,
        "ligare.toml",
        &format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\n{body}"),
    );
}

fn collect_project(root: &Path) -> Result<Compiler<'static>, ligare::diagnostic::Diagnostic> {
    let project = resolve_project(root, UpdateMode::Locked)?;
    write_lock(root, &project.lock)?;
    let bump = Box::leak(Box::new(Bump::new()));
    let arena = Box::leak(Box::new(TermArena::new(bump)));
    let mut compiler = Compiler::new(bump, arena);
    let entry = root.join(&project.manifest.entry);
    compiler.collect_project_entry(root, &entry, project.graph)?;
    Ok(compiler)
}

#[test]
fn resolves_multi_package_local_dependencies_and_cross_package_use() {
    let root = temp_project();
    let util = root.join("util");
    manifest(&util, "util", "");
    write(
        &util,
        "src/main.lig",
        "pub mod math\npub def ignored : int := 0\n",
    );
    write(
        &util,
        "src/math.lig",
        "pub def inc (x : int) : int := x + 1\n",
    );
    manifest(
        &root,
        "app",
        "\n[dependencies]\nutil = { path = \"util\" }\n",
    );
    write(
        &root,
        "src/main.lig",
        "use util::math::inc\npub def main : IO () := let _ := inc 1 in ()\n",
    );

    let compiler = collect_project(&root).unwrap();
    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "util::math::inc")
    }));
    let lock = fs::read_to_string(root.join("ligare.lock")).unwrap();
    assert!(lock.contains("name = \"util\""), "{lock}");
    assert!(lock.contains("version = \"local\""), "{lock}");
}

#[test]
fn collect_project_writes_file_cache_to_each_package_target_dir() {
    let root = temp_project();
    let util = root.join("util");
    manifest(&util, "util", "");
    let util_main = "pub mod math\npub def ignored : int := 0\n";
    let util_math = "pub def inc (x : int) : int := x + 1\n";
    write(&util, "src/main.lig", util_main);
    write(&util, "src/math.lig", util_math);
    manifest(
        &root,
        "app",
        "\n[dependencies]\nutil = { path = \"util\" }\n",
    );
    let app_main = "use util::math::inc\npub def main : IO () := let _ := inc 1 in ()\n";
    write(&root, "src/main.lig", app_main);

    collect_project(&root).unwrap();

    let app_cache = PackageCompilerCache::load(&root, &root, "app");
    let util_cache = PackageCompilerCache::load(&root, &util, "util");
    assert!(app_cache.is_fresh(&root.join("src/main.lig"), source_hash(app_main)));
    assert!(util_cache.is_fresh(&util.join("src/math.lig"), source_hash(util_math)));
    assert!(cache_file_path(&root, "app").exists());
    assert!(cache_file_path(&root, "util").exists());
    assert!(!cache_file_path(&util, "util").exists());
}

#[test]
fn lib_dependency_without_entry_defaults_to_lib_lig() {
    let root = temp_project();
    let std = root.join("std");
    manifest(&std, "std", "type = \"lib\"\n");
    write(&std, "src/lib.lig", "pub mod io\n");
    write(
        &std,
        "src/io.lig",
        "pub def put_str (s : str) : IO () := ()\n",
    );
    manifest(&root, "app", "\n[dependencies]\nstd = { path = \"std\" }\n");
    write(
        &root,
        "src/main.lig",
        "use std::io::put_str\npub def main : IO () := put_str \"ok\"\n",
    );

    let project = resolve_project(&root, UpdateMode::Locked).unwrap();
    assert_eq!(project.graph.packages["std"].root, std.join("src"));
    assert_eq!(project.manifest.entry, PathBuf::from("src/main.lig"));
    let compiler = collect_project(&root).unwrap();
    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "std::io::put_str")
    }));
}

#[test]
fn package_without_type_defaults_to_lib_when_only_lib_entry_exists() {
    let root = temp_project();
    manifest(&root, "math", "");
    write(
        &root,
        "src/lib.lig",
        "pub def add_one (x : int) : int := x + 1\n",
    );

    let project = resolve_project(&root, UpdateMode::Locked).unwrap();
    assert_eq!(project.manifest.entry, PathBuf::from("src/lib.lig"));
    assert_eq!(project.manifest.package_type, PackageType::Lib);
}

#[test]
fn package_without_type_defaults_to_binary_when_main_entry_exists() {
    let root = temp_project();
    manifest(&root, "app", "");
    write(&root, "src/main.lig", "pub def main : IO () := ()\n");

    let project = resolve_project(&root, UpdateMode::Locked).unwrap();
    assert_eq!(project.manifest.entry, PathBuf::from("src/main.lig"));
    assert_eq!(project.manifest.package_type, PackageType::Binary);
}

#[test]
fn package_cycle_is_rejected() {
    let root = temp_project();
    let a = root.join("a");
    let b = root.join("a/b");
    manifest(
        &a,
        "a",
        "\n[dependencies]\nb = { path = \"b\", version = \"local\" }\n",
    );
    manifest(
        &b,
        "b",
        "\n[dependencies]\na = { path = \"..\", version = \"local\" }\n",
    );
    write(&a, "src/main.lig", "pub def a_value : int := 1\n");
    write(&b, "src/main.lig", "pub def b_value : int := 1\n");
    manifest(
        &root,
        "app",
        "\n[dependencies]\na = { path = \"a\", version = \"local\" }\n",
    );
    write(
        &root,
        "src/main.lig",
        "use a::main::a_value\npub def main : IO () := a_value\n",
    );

    let err = resolve_project(&root, UpdateMode::Locked).unwrap_err();
    assert!(err.message.contains("cyclic package dependency"), "{err:?}");
}

#[test]
fn lock_file_pins_git_version_until_update() {
    let _guard = env_lock().lock().unwrap();
    let root = temp_project();
    unsafe {
        std::env::set_var("LIGARE_HOME", root.join(".ligare"));
    }
    let repo = root.join("dep_repo");
    init_git_dep(&repo);

    manifest(
        &root,
        "app",
        &format!(
            "\n[dependencies]\nlib = {{ git = \"{}\", version = \"v1\" }}\n",
            repo.canonicalize().unwrap().display()
        ),
    );
    write(
        &root,
        "src/main.lig",
        "use lib::api::value\npub def main : IO () := value\n",
    );

    let first = resolve_project(&root, UpdateMode::Locked).unwrap();
    write_lock(&root, &first.lock).unwrap();
    let pinned = first.lock.deps["lib"].commit.clone();

    git_dep_commit(&repo, "2", "v2");
    let locked = resolve_project(&root, UpdateMode::Locked).unwrap();
    assert_eq!(locked.lock.deps["lib"].commit, pinned);

    let updated = resolve_project(
        &root,
        UpdateMode::Version {
            name: "lib".to_string(),
            version: "v2".to_string(),
        },
    )
    .unwrap();
    assert_ne!(updated.lock.deps["lib"].commit, pinned);
}

#[test]
fn non_exported_dependency_module_is_rejected() {
    let root = temp_project();
    let util = root.join("util");
    manifest(&util, "util", "");
    write(
        &util,
        "src/main.lig",
        "pub mod public\nmod private\npub def ignored : int := 0\n",
    );
    write(&util, "src/public.lig", "pub def visible : int := 1\n");
    write(&util, "src/private.lig", "pub def hidden : int := 1\n");
    manifest(
        &root,
        "app",
        "\n[dependencies]\nutil = { path = \"util\" }\n",
    );
    write(
        &root,
        "src/main.lig",
        "use util::private::hidden\npub def main : IO () := hidden\n",
    );

    let err = match collect_project(&root) {
        Ok(_) => panic!("expected private module import to fail"),
        Err(err) => err,
    };
    assert!(err.message.contains("not exported"), "{err:?}");
}

#[test]
fn cli_new_creates_binary_package() {
    let root = temp_project();
    let package = root.join("hello-world");

    let bin = env!("CARGO_BIN_EXE_ligare");
    let status = Command::new(bin)
        .args(["new", package.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());

    let manifest = fs::read_to_string(package.join("ligare.toml")).unwrap();
    assert!(manifest.contains("name = \"hello_world\""), "{manifest}");
    assert!(manifest.contains("type = \"binary\""), "{manifest}");
    let main = fs::read_to_string(package.join("src/main.lig")).unwrap();
    assert_eq!(main, "pub def main : IO () := ()\n");

    let status = Command::new(bin)
        .args(["build", package.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());
    assert!(package.join("target").join("hello_world").exists());
}

#[test]
fn cli_new_creates_library_package() {
    let root = temp_project();
    let package = root.join("math");

    let bin = env!("CARGO_BIN_EXE_ligare");
    let status = Command::new(bin)
        .args(["new", "--lib", package.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());

    let manifest = fs::read_to_string(package.join("ligare.toml")).unwrap();
    assert!(manifest.contains("name = \"math\""), "{manifest}");
    assert!(manifest.contains("type = \"lib\""), "{manifest}");
    assert!(manifest.contains("entry = \"src/lib.lig\""), "{manifest}");
    let lib = fs::read_to_string(package.join("src/lib.lig")).unwrap();
    assert_eq!(lib, "pub def hello : str := \"hello\"\n");

    let status = Command::new(bin)
        .args(["build", package.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());
    assert!(package.join("target").join("math.c").exists());
}

#[test]
fn cli_new_rejects_non_empty_directory() {
    let root = temp_project();
    write(&root, "README.md", "keep me\n");

    let bin = env!("CARGO_BIN_EXE_ligare");
    let status = Command::new(bin)
        .args(["new", root.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(!status.success());
    assert_eq!(
        fs::read_to_string(root.join("README.md")).unwrap(),
        "keep me\n"
    );
    assert!(!root.join("ligare.toml").exists());
}

#[test]
fn cli_test_scans_lig_test_files() {
    let root = temp_project();
    manifest(&root, "app", "");
    write(&root, "src/main.lig", "pub def main : IO () := ()\n");
    write(
        &root,
        "src/math_test.lig",
        "pub def main : IO () := ()\n#check 1 : int\n",
    );
    let bin = env!("CARGO_BIN_EXE_ligare");
    let status = Command::new(bin)
        .args(["test", root.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());
}

#[test]
fn cli_build_writes_binary_to_package_target_dir() {
    let root = temp_project();
    manifest(&root, "app", "type = \"binary\"\n");
    write(&root, "src/main.lig", "pub def main : IO () := ()\n");

    let bin = env!("CARGO_BIN_EXE_ligare");
    let status = Command::new(bin)
        .args(["build", root.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());
    assert!(root.join("target").join("app").exists());
}

#[test]
fn cli_build_lib_package_writes_c_without_main_entry() {
    let root = temp_project();
    manifest(&root, "math", "type = \"lib\"\nentry = \"src/lib.lig\"\n");
    write(
        &root,
        "src/lib.lig",
        "pub def add_one (x : int) : int := x + 1\n",
    );

    let bin = env!("CARGO_BIN_EXE_ligare");
    let status = Command::new(bin)
        .args(["build", root.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());
    let c = fs::read_to_string(root.join("target").join("math.c")).unwrap();
    assert!(c.contains("add_one"), "{c}");
}

#[test]
fn cli_build_infers_lib_package_from_lib_entry() {
    let root = temp_project();
    manifest(&root, "math", "entry = \"src/lib.lig\"\n");
    write(
        &root,
        "src/lib.lig",
        "pub def add_one (x : int) : int := x + 1\n",
    );

    let bin = env!("CARGO_BIN_EXE_ligare");
    let status = Command::new(bin)
        .args(["build", root.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());
    assert!(root.join("target").join("math.c").exists());
}

fn init_git_dep(repo: &Path) {
    fs::create_dir_all(repo).unwrap();
    manifest(repo, "lib", "");
    write(
        repo,
        "src/main.lig",
        "pub mod api\npub def ignored : int := 0\n",
    );
    write(repo, "src/api.lig", "pub def value : int := 1\n");
    run(repo, &["init"]);
    run(repo, &["config", "user.email", "test@example.com"]);
    run(repo, &["config", "user.name", "Test"]);
    run(repo, &["add", "."]);
    run(repo, &["commit", "-m", "v1"]);
    run(repo, &["tag", "v1"]);
}

fn git_dep_commit(repo: &Path, value: &str, tag: &str) {
    write(
        repo,
        "src/api.lig",
        &format!("pub def value : int := {value}\n"),
    );
    run(repo, &["add", "."]);
    run(repo, &["commit", "-m", tag]);
    run(repo, &["tag", tag]);
}

fn run(root: &Path, args: &[&str]) {
    let status = Command::new("git")
        .args(args)
        .current_dir(root)
        .status()
        .unwrap();
    assert!(status.success(), "git {}", args.join(" "));
}
