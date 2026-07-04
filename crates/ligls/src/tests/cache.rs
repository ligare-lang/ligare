use super::*;

#[test]
fn cache_rechecks_only_changed_item_and_direct_dependents() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let first = r#"
def a : int := 1
def b : int := a
def c : int := 2
"#;
    let changed_independent = r#"
def a : int := 1
def b : int := a
def c : int := 3
"#;
    let changed_dependency = r#"
def a : int := 10
def b : int := a
def c : int := 3
"#;

    let initial = cache.update_fast(uri.clone(), Some(1), first.to_string());
    assert_eq!(initial.dirty_items, vec!["a", "b", "c"]);

    let local = cache.update_fast(uri.clone(), Some(2), changed_independent.to_string());
    assert_eq!(local.dirty_items, vec!["c"]);

    let dependent = cache.update_fast(uri.clone(), Some(3), changed_dependency.to_string());
    assert_eq!(dependent.dirty_items, vec!["a", "b"]);
}

#[test]
fn cache_marks_cross_module_direct_dependents_dirty() {
    let mut cache = LspCache::new();
    let math_uri = lsp::Url::parse("file:///workspace/math.lig").unwrap();
    let main_uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let math = "pub def one : int := 1\n";
    let main = r#"
mod math
use math::one
pub def main : IO () := let _ := one in ()
"#;

    cache.update_fast(main_uri.clone(), Some(1), main.to_string());
    cache.update_fast(math_uri.clone(), Some(1), math.to_string());
    let summary = cache.cache_summary(&math_uri).expect("math cache");
    assert_eq!(summary.ast_items, 1);
    assert_eq!(summary.symbols, 1);
    assert_eq!(summary.exports, vec!["one"]);
    assert_eq!(summary.items, 1);

    let update = cache.update_fast(math_uri, Some(2), "pub def one : int := 2\n".to_string());

    assert_eq!(update.dirty_dependents, vec![main_uri]);
}

#[test]
fn cache_reports_unknown_use_module() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "use missing::thing\n#check 1 : int\n";

    let update = cache.update_fast(uri, Some(1), source.to_string());

    assert!(
        update
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("module not found: missing")),
        "{:#?}",
        update.diagnostics
    );
}

#[test]
fn cache_reports_incomplete_use_path() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "use abcd\n#check 1 : int\n";

    let update = cache.update_fast(uri, Some(1), source.to_string());

    assert!(
        update.diagnostics.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("use path must include a module and symbol")
        }),
        "{:#?}",
        update.diagnostics
    );
}

#[test]
fn cache_resolves_wildcard_use_imports() {
    let mut cache = LspCache::new();
    let math_uri = lsp::Url::parse("file:///workspace/math.lig").unwrap();
    let main_uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();

    cache.update_fast(math_uri, Some(1), "pub def one : int := 1\n".to_string());
    let update = cache.update_fast(
        main_uri,
        Some(1),
        "mod math\nuse math::*\n#check one : int\n".to_string(),
    );

    assert!(update.diagnostics.is_empty(), "{:#?}", update.diagnostics);
}

#[test]
fn cache_reports_unknown_declared_module() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "mod missing\n#check 1 : int\n";

    let update = cache.update_fast(uri, Some(1), source.to_string());

    assert!(
        update
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("module not found: missing")),
        "{:#?}",
        update.diagnostics
    );
}

#[test]
fn cache_reports_duplicate_imports() {
    let mut cache = LspCache::new();
    let math_uri = lsp::Url::parse("file:///workspace/math.lig").unwrap();
    let main_uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let math = "pub def one : int := 1\n";
    let main = "mod math\nuse math::one\nuse math::one\n#check one : int\n";

    cache.update_fast(math_uri, Some(1), math.to_string());
    let update = cache.update_fast(main_uri, Some(1), main.to_string());

    assert!(
        update
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("duplicate import `one`")),
        "{:#?}",
        update.diagnostics
    );
}

#[test]
fn cache_hit_rate_tracks_item_reuse() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let first = "def a : int := 1\ndef b : int := a\ndef c : int := 2\n";
    let second = "def a : int := 1\ndef b : int := a\ndef c : int := 3\n";

    cache.update_fast(uri.clone(), Some(1), first.to_string());
    cache.update_fast(uri.clone(), Some(2), second.to_string());
    cache.update_fast(uri, Some(2), second.to_string());
    let stats = cache.stats();

    assert_eq!(stats.file_hits, 1);
    assert_eq!(stats.file_misses, 2);
    assert_eq!(stats.item_hits, 2);
    assert_eq!(stats.item_misses, 4);
    assert!((stats.item_hit_rate() - (2.0 / 6.0)).abs() < f64::EPSILON);
}

#[test]
fn full_check_updates_and_reuses_package_compiler_cache() {
    let root = std::env::temp_dir().join(format!(
        "ligare_lsp_compiler_cache_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("ligare.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let source = "pub def main : IO () := ()\n";
    let path = root.join("src/main.lig");
    std::fs::write(&path, source).unwrap();
    let uri = lsp::Url::from_file_path(&path).unwrap();
    let mut cache = LspCache::new();

    let initial = cache.update_full(uri.clone(), Some(1), source.to_string());
    assert!(initial.diagnostics.is_empty(), "{:#?}", initial.diagnostics);
    assert!(PackageCompilerCache::load(&root, &root, "app").is_fresh(&path, source_hash(source)));

    let reused = cache.update_full(uri, Some(2), source.to_string());
    assert!(reused.diagnostics.is_empty(), "{:#?}", reused.diagnostics);
    assert_eq!(cache.stats().compiler_cache_hits, 1);
}

#[test]
fn full_check_writes_dependency_cache_under_workspace_package_target() {
    let root = std::env::temp_dir().join(format!(
        "ligare_lsp_dep_compiler_cache_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let util = root.join("util");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::create_dir_all(util.join("src")).unwrap();
    std::fs::write(
        root.join("ligare.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies]\nutil = { path = \"util\" }\n",
    )
    .unwrap();
    std::fs::write(
        util.join("ligare.toml"),
        "[package]\nname = \"util\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    std::fs::write(util.join("src/main.lig"), "pub mod math\n").unwrap();
    let main_source = "use util::math::inc\npub def main : IO () := let _ := inc 1 in ()\n";
    let util_source = "pub def inc (x : int) : int := x + 1\n";
    let main_path = root.join("src/main.lig");
    let util_path = util.join("src/math.lig");
    std::fs::write(&main_path, main_source).unwrap();
    std::fs::write(&util_path, util_source).unwrap();
    let main_uri = lsp::Url::from_file_path(&main_path).unwrap();
    let util_uri = lsp::Url::from_file_path(&util_path).unwrap();
    let mut cache = LspCache::new();

    cache.update_fast(main_uri, Some(1), main_source.to_string());
    let update = cache.update_full(util_uri, Some(1), util_source.to_string());

    assert!(update.diagnostics.is_empty(), "{:#?}", update.diagnostics);
    assert!(
        PackageCompilerCache::load(&root, &util, "util")
            .is_fresh(&util_path, source_hash(util_source))
    );
    assert!(cache_file_path(&root, "util").exists());
    assert!(!cache_file_path(&util, "util").exists());
}
