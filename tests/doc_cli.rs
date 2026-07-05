use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn temp_project() -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "ligare_doc_cli_{}_{}_{}",
        std::process::id(),
        nanos,
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(dir.join("src")).unwrap();
    dir
}

#[test]
fn cli_doc_generates_markdown_for_source_tree() {
    let root = temp_project();
    fs::write(
        root.join("src/main.lig"),
        "-- | Adds one\npub def inc (x : int) : int := x + 1\n",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_ligare"))
        .arg("doc")
        .arg(&root)
        .output()
        .expect("ligare doc should run");

    assert!(
        output.status.success(),
        "status: {:?}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("# `src/main.lig`"), "{stdout}");
    assert!(stdout.contains("## `inc`"), "{stdout}");
    assert!(stdout.contains("Adds one"), "{stdout}");
    assert!(stdout.contains("pub def inc (x : int) : int"), "{stdout}");
}
