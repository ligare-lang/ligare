use bumpalo::Bump;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::package::{UpdateMode, resolve_project, write_lock};
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
        &format!("[package]\nname = \"{name}\"\n{body}"),
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
    manifest(&util, "util", "\n[exports]\nmodules = [\"math\"]\n");
    write(&util, "src/main.lig", "pub def ignored : int := 0\n");
    write(
        &util,
        "src/math.lig",
        "pub def inc (x : int) : int := x + 1\n",
    );
    manifest(
        &root,
        "app",
        "\n[dependencies]\nutil = { path = \"util\", version = \"local\" }\n",
    );
    write(
        &root,
        "src/main.lig",
        "use util::math::inc\npub def main : IO Unit := let _ := inc 1 in Unit\n",
    );

    let compiler = collect_project(&root).unwrap();
    assert!(compiler.raw_defs().iter().any(|top| {
        matches!(top, ligare::front::parser::TopLevel::TLDef(name, ..) if *name == "util::math::inc")
    }));
    let lock = fs::read_to_string(root.join("ligare.lock")).unwrap();
    assert!(lock.contains("name = \"util\""), "{lock}");
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
        "use a::main::a_value\npub def main : IO Unit := a_value\n",
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
        "use lib::api::value\npub def main : IO Unit := value\n",
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
    manifest(&util, "util", "\n[exports]\nmodules = [\"public\"]\n");
    write(&util, "src/main.lig", "pub def ignored : int := 0\n");
    write(&util, "src/private.lig", "pub def hidden : int := 1\n");
    manifest(
        &root,
        "app",
        "\n[dependencies]\nutil = { path = \"util\", version = \"local\" }\n",
    );
    write(
        &root,
        "src/main.lig",
        "use util::private::hidden\npub def main : IO Unit := hidden\n",
    );

    let err = match collect_project(&root) {
        Ok(_) => panic!("expected private module import to fail"),
        Err(err) => err,
    };
    assert!(err.message.contains("not exported"), "{err:?}");
}

#[test]
fn cli_test_scans_lig_test_files() {
    let root = temp_project();
    manifest(&root, "app", "");
    write(&root, "src/main.lig", "pub def main : IO Unit := Unit\n");
    write(
        &root,
        "src/math_test.lig",
        "pub def main : IO Unit := Unit\n#check 1 : int\n",
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
    manifest(&root, "app", "");
    write(&root, "src/main.lig", "pub def main : IO Unit := Unit\n");

    let bin = env!("CARGO_BIN_EXE_ligare");
    let status = Command::new(bin)
        .args(["build", root.to_str().unwrap()])
        .status()
        .unwrap();
    assert!(status.success());
    assert!(root.join("target").join("app").exists());
}

fn init_git_dep(repo: &Path) {
    fs::create_dir_all(repo).unwrap();
    manifest(repo, "lib", "\n[exports]\nmodules = [\"api\"]\n");
    write(repo, "src/main.lig", "pub def ignored : int := 0\n");
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
