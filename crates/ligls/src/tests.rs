use std::sync::Arc;

use bumpalo::Bump;
use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::compiler::cache::{PackageCompilerCache, cache_file_path, source_hash};
use ligare::config::GLOBAL_ALLOCATOR_NAME_PREFIX;
use ligare::core::pool::TermArena;
use ligare::core::syntax::Term;
use ligare::front::parser::{TopLevel, Visibility};
use tokio::sync::Mutex;
use tokio::time::{Duration, Instant};
use tower_lsp::lsp_types as lsp;

use crate::cache::LspCache;
use crate::semantic::decode_semantic_tokens;
use crate::text::{offset_to_position, position_to_offset};
use crate::{
    AstNode, DiagnosticCheck, DiagnosticPublisher, DiagnosticService, completion_items_for_source,
    lsp_diagnostics_for_source, parse_program_lsp,
};

fn arena() -> (&'static Bump, TermArena<'static>) {
    let bump = Box::leak(Box::new(Bump::new()));
    (bump, TermArena::new(bump))
}

#[test]
fn normal_program_reuses_ligare_ast() {
    let (bump, arena) = arena();
    let source = r#"
mod app
pub use std::io
def Point : prop := struct
  x : int
  y : int
def Option : prop := enum
  | None
  | Some of (value : int)
def main : int := match Option.Some 1 with | Some value => value | None => 0
#eval Point.x
"#;

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(ast.top_levels().count(), 6);
    assert!(matches!(
        ast.items[0],
        AstNode::TopLevel(TopLevel::TLMod(..))
    ));
    assert!(matches!(
        ast.items[1],
        AstNode::TopLevel(TopLevel::TLUse(_, Visibility::Public, _))
    ));
    assert!(matches!(
        ast.items[5],
        AstNode::TopLevel(TopLevel::TLEval(term, _)) if matches!(*term, Term::Named("Point.x"))
    ));
}

#[test]
fn global_allocator_attribute_is_parsed_with_following_def() {
    let (bump, arena) = arena();
    let source = "#[global_allocator]\ndef alloc : int := 1\ndef after : int := 2";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(ast.top_levels().count(), 2);
    let alloc_name = format!("{GLOBAL_ALLOCATOR_NAME_PREFIX}alloc");
    assert!(
        matches!(ast.items[0], AstNode::TopLevel(TopLevel::TLDef(name, ..)) if name == alloc_name)
    );
    assert!(
        matches!(ast.items[1], AstNode::TopLevel(TopLevel::TLDef(name, ..)) if name == "after")
    );
}

#[test]
fn shared_constraint_param_group_reuses_ligare_ast() {
    let (bump, arena) = arena();
    let source = "def add (a b : int) : int := a + b";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(ast.top_levels().count(), 1);
    assert!(
        matches!(ast.items[0], AstNode::TopLevel(TopLevel::TLDef(_, params, _, _, _)) if params.len() == 2)
    );
}

#[test]
fn single_error_produces_partial_ast_and_error_node() {
    let (bump, arena) = arena();
    let source = "def good : int := 1\ndef broken : int := if true then\n#eval good";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(!errors.is_empty());
    assert!(matches!(
        ast.items[0],
        AstNode::TopLevel(TopLevel::TLDef(..))
    ));
    assert!(matches!(ast.items[1], AstNode::Error(_)));
    assert!(matches!(
        ast.items[2],
        AstNode::TopLevel(TopLevel::TLEval(..))
    ));
}

#[test]
fn bare_top_level_expression_does_not_emit_header_error() {
    let (bump, arena) = arena();

    let (ast, errors) = parse_program_lsp("1 + 2", bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert!(matches!(
        ast.items[0],
        AstNode::TopLevel(TopLevel::TLExpr(..))
    ));
}

#[test]
fn multiple_errors_are_reported_and_recovered() {
    let (bump, arena) = arena();
    let source = "def := 1\ndef ok : int := 2\n#check : int\ndef tail : int := 3";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.len() >= 2, "{errors:?}");
    assert!(matches!(ast.items[0], AstNode::Error(_)));
    assert!(matches!(
        ast.items[1],
        AstNode::TopLevel(TopLevel::TLDef(..))
    ));
    assert!(matches!(ast.items[2], AstNode::Error(_)));
    assert!(matches!(
        ast.items[3],
        AstNode::TopLevel(TopLevel::TLDef(..))
    ));
}

#[test]
fn nested_error_does_not_hide_following_definition() {
    let (bump, arena) = arena();
    let source = r#"
def bad : int := do {
  let x := 1;
  if true then 1 else
def after : int := 42
"#;

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(!errors.is_empty());
    assert!(matches!(ast.items[0], AstNode::Error(_)));
    assert!(
        matches!(ast.items[1], AstNode::TopLevel(TopLevel::TLDef(name, ..)) if name == "after")
    );
}

#[test]
fn diagnostics_check_eval_like_forms_in_quiet_mode() {
    for source in ["#eval missing", "missing"] {
        let diagnostics = lsp_diagnostics_for_source(source, DiagnosticCheck::Fast);
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("unbound: missing")),
            "{diagnostics:#?}"
        );
    }
}

#[derive(Clone, Default)]
struct RecordingPublisher {
    notifications: Arc<Mutex<Vec<(lsp::Url, Vec<lsp::Diagnostic>, Option<i32>)>>>,
}

#[tower_lsp::async_trait]
impl DiagnosticPublisher for RecordingPublisher {
    async fn publish_diagnostics(
        &self,
        uri: lsp::Url,
        diagnostics: Vec<lsp::Diagnostic>,
        version: Option<i32>,
    ) {
        self.notifications
            .lock()
            .await
            .push((uri, diagnostics, version));
    }
}

impl RecordingPublisher {
    async fn wait_for_notifications(
        &self,
        count: usize,
    ) -> Vec<(lsp::Url, Vec<lsp::Diagnostic>, Option<i32>)> {
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            let notifications = self.notifications.lock().await.clone();
            if notifications.len() >= count {
                return notifications;
            }
            assert!(
                Instant::now() < deadline,
                "timed out waiting for {count} diagnostic notifications"
            );
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }
}

#[tokio::test]
async fn change_notification_contains_parse_and_type_errors() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher.clone());
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "def good : int := 1\ndef broken : int := if true then\n#check true : int";

    service
        .did_change(
            uri.clone(),
            Some(1),
            vec![lsp::TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: source.to_string(),
            }],
        )
        .await;

    let notifications = publisher.wait_for_notifications(1).await;
    let (_, diagnostics, version) = notifications.last().unwrap();
    assert_eq!(*version, Some(1));
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("parse error")
                || diagnostic.message.contains("unexpected")),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("check failed")
                && diagnostic.message.contains("expected int")),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.severity == Some(lsp::DiagnosticSeverity::ERROR))
    );
}

#[tokio::test]
async fn fast_and_full_check_notifications_are_consistent_and_deduplicated() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher.clone());
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "#check true : int";

    service
        .did_change(
            uri,
            Some(7),
            vec![lsp::TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: source.to_string(),
            }],
        )
        .await;

    let notifications = publisher.wait_for_notifications(2).await;
    let fast = &notifications[0].1;
    let full = &notifications[1].1;
    assert_eq!(diagnostic_keys(fast), diagnostic_keys(full));
    assert_eq!(full.len(), diagnostic_keys(full).len());
}

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

#[tokio::test]
async fn service_publishes_module_import_diagnostics() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher.clone());
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "mod missing\nuse abcd\nuse missing::thing\nuse missing::thing\n#check 1 : int\n";

    service
        .did_open(uri.clone(), Some(1), source.to_string())
        .await;

    let notifications = publisher.wait_for_notifications(1).await;
    let (_, diagnostics, version) = notifications.last().unwrap();
    assert_eq!(*version, Some(1));
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("module not found: missing")),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("use path must include a module and symbol")),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("duplicate import `thing`")),
        "{diagnostics:#?}"
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

#[test]
fn semantic_tokens_classify_semantic_identifier_kinds() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
mod math
pub use std::io::print
pub def Option : prop := enum
  | None
  | Some of (value : int)
def Point : prop := struct
  x : int
def add (x : int) (y : int) : int := x + y
def opt : Option := Some 1
#check let p : Point := Point.mk 1 in Point.x p : int
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "def", "keyword");
    assert_token(&decoded, "add", "function");
    assert_token(&decoded, "opt", "variable");
    assert_token(&decoded, "Some", "constructor");
    assert_token(&decoded, "Option", "constraint");
    assert_token(&decoded, "Point", "constraint");
    assert_token(&decoded, "math", "namespace");
    assert_token(&decoded, "std", "namespace");
    assert_token(&decoded, "x", "parameter");
    assert!(
        decoded.iter().any(|token| {
            token.text == "Option"
                && token.kind == "constraint"
                && token.modifiers.contains(&"public")
        }),
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_namespace_members_and_qualified_references() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
namespace Ops {
  pub def inc (x : int) : int := x + 1
  pub def Flag : prop := enum
    | On
}
#eval Ops::inc 1
#check Ops::On : Ops::Flag
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert!(
        decoded
            .iter()
            .filter(|token| token.text == "Ops" && token.kind == "namespace")
            .count()
            >= 3,
        "{decoded:#?}"
    );
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "inc" && token.kind == "function")
            .count(),
        2,
        "{decoded:#?}"
    );
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "Flag" && token.kind == "constraint")
            .count(),
        2,
        "{decoded:#?}"
    );
    assert_token(&decoded, "On", "constructor");
}

#[test]
fn semantic_tokens_legend_exposes_constraints_as_lsp_types() {
    let legend = crate::semantic_tokens_legend();

    assert_eq!(
        legend.token_types[3],
        lsp::SemanticTokenType::TYPE,
        "semantic constraints are user-facing types and should use the standard LSP token type"
    );
}

#[test]
fn semantic_tokens_classify_builtin_constraints() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = format!(
        "#check 0 : {}\n",
        BUILTIN_CONSTRAINT_NAMES.join("\n#check 0 : ")
    );

    cache.update_fast(uri.clone(), Some(1), source.clone());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(&source, &tokens);

    for builtin in BUILTIN_CONSTRAINT_NAMES {
        assert_token(&decoded, builtin, "constraint");
    }
}

#[test]
fn semantic_tokens_classify_refinement_constraint_aliases() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def Nat := int where (x => x >= 0)
def zero : Nat := 0
#check zero : Nat
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert!(
        decoded.iter().any(|token| {
            token.text == "Nat"
                && token.kind == "constraint"
                && token.modifiers.contains(&"definition")
        }),
        "{decoded:#?}"
    );
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "Nat" && token.kind == "constraint")
            .count(),
        3,
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_parameterized_constraint_definitions() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def Option (A : prop) : prop := enum
  | None
  | Some of (value : A)
def maybe : Option int := Some 1
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert!(
        decoded.iter().any(|token| {
            token.text == "Option"
                && token.kind == "constraint"
                && token.modifiers.contains(&"definition")
        }),
        "{decoded:#?}"
    );
    assert!(
        decoded
            .iter()
            .any(|token| token.text == "Option" && token.kind == "constraint"),
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_type_parameters_as_constraints() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def id (A : prop) (x : A) : A := x
def Option (A : prop) : prop := enum
  | None
  | Some of (value : A)
def map (A : prop) (opt : Option A) : Option A := opt
def implicit {B : prop} (y : B) : B := y
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "A" && token.kind == "constraint")
            .count(),
        8,
        "{decoded:#?}"
    );
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "B" && token.kind == "constraint")
            .count(),
        3,
        "{decoded:#?}"
    );
    assert_token(&decoded, "x", "parameter");
    assert_token(&decoded, "y", "parameter");
    assert!(
        decoded
            .iter()
            .all(|token| !matches!(token.text.as_str(), "A" | "B") || token.kind != "parameter"),
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_interface_instances() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def ShowInt : prop := struct
  show : int -> str
def show_int (x : int) : str := "int"
instance showInt : ShowInt := ShowInt.mk show_int
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "instance", "keyword");
    assert_token(&decoded, "showInt", "variable");
    assert_token(&decoded, "ShowInt", "constraint");
}

#[test]
fn semantic_tokens_update_after_file_change() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let first = "def value : int := 1\n#check value : int\n";
    let second = "def value (x : int) : int := x\n#check value 1 : int\n";

    cache.update_fast(uri.clone(), Some(1), first.to_string());
    let first_tokens = cache.semantic_tokens(&uri).expect("first semantic tokens");
    let first_decoded = decode_semantic_tokens(first, &first_tokens);
    assert_token(&first_decoded, "value", "variable");

    cache.update_fast(uri.clone(), Some(2), second.to_string());
    let second_tokens = cache.semantic_tokens(&uri).expect("second semantic tokens");
    let second_decoded = decode_semantic_tokens(second, &second_tokens);
    assert_token(&second_decoded, "value", "function");
    assert_token(&second_decoded, "x", "parameter");
}

#[test]
fn semantic_tokens_highlight_comments_without_classifying_comment_text() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
-- def hidden : int := value
{- pub def also_hidden : int := 0 -}
def value : int := /- inline int value -/ 1
/-
def fake : int := value
-/
#check value : int
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "-- def hidden : int := value", "comment");
    assert_token(&decoded, "{- pub def also_hidden : int := 0 -}", "comment");
    assert_token(&decoded, "/- inline int value -/", "comment");
    assert_token(&decoded, "def fake : int := value", "comment");
    assert_token(&decoded, "value", "variable");
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "value" && token.kind == "variable")
            .count(),
        2,
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_keep_classification_after_block_comment_in_declaration() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "def value : int := /- comment -/ 1\n#check value : int\n";

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "/- comment -/", "comment");
    assert_token(&decoded, "value", "variable");
    assert_token(&decoded, "int", "constraint");
}

fn diagnostic_keys(
    diagnostics: &[lsp::Diagnostic],
) -> std::collections::HashSet<(u32, u32, u32, u32, String)> {
    diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.range.start.line,
                diagnostic.range.start.character,
                diagnostic.range.end.line,
                diagnostic.range.end.character,
                diagnostic.message.clone(),
            )
        })
        .collect()
}

fn assert_token(tokens: &[crate::semantic::DecodedSemanticToken], text: &str, kind: &str) {
    assert!(
        tokens
            .iter()
            .any(|token| token.text == text && token.kind == kind),
        "missing {kind} token `{text}` in {tokens:#?}"
    );
}

fn source_and_position(marked: &str) -> (String, lsp::Position) {
    let offset = marked.find("<|>").expect("missing completion marker");
    let source = marked.replace("<|>", "");
    let position = offset_to_position(&source, offset);
    (source, position)
}

fn range_text(source: &str, range: lsp::Range) -> &str {
    let start = position_to_offset(source, range.start).unwrap();
    let end = position_to_offset(source, range.end).unwrap();
    &source[start..end]
}

fn hover_markdown(hover: lsp::Hover) -> String {
    match hover.contents {
        lsp::HoverContents::Markup(markup) => markup.value,
        lsp::HoverContents::Scalar(lsp::MarkedString::String(value)) => value,
        lsp::HoverContents::Scalar(lsp::MarkedString::LanguageString(value)) => value.value,
        lsp::HoverContents::Array(values) => values
            .into_iter()
            .map(|value| match value {
                lsp::MarkedString::String(value) => value,
                lsp::MarkedString::LanguageString(value) => value.value,
            })
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

fn completion_labels(marked: &str) -> Vec<String> {
    let (source, position) = source_and_position(marked);
    completion_items_for_source(&source, position)
        .into_iter()
        .map(|item| item.label)
        .collect()
}

fn assert_label_before(labels: &[String], earlier: &str, later: &str) {
    let earlier_idx = labels
        .iter()
        .position(|label| label == earlier)
        .unwrap_or_else(|| panic!("missing completion `{earlier}` in {labels:?}"));
    let later_idx = labels
        .iter()
        .position(|label| label == later)
        .unwrap_or_else(|| panic!("missing completion `{later}` in {labels:?}"));
    assert!(
        earlier_idx < later_idx,
        "expected `{earlier}` before `{later}` in {labels:?}"
    );
}

#[test]
fn completion_filters_function_argument_by_explicit_constraint() {
    let labels = completion_labels(
        r#"
def add (x : int) (y : int) : int := x + y
def count : int := 1
def truth : bool := true
#eval add <|>
"#,
    );

    assert!(labels.contains(&"count".to_string()), "{labels:?}");
    assert!(!labels.contains(&"truth".to_string()), "{labels:?}");
}

#[test]
fn completion_uses_let_binding_rhs_constraint() {
    let labels = completion_labels(
        r#"
def good : int := 1
def bad : bool := true
def main : int := let x : int := <|> in x
"#,
    );

    assert!(labels.contains(&"good".to_string()), "{labels:?}");
    assert!(!labels.contains(&"bad".to_string()), "{labels:?}");
}

#[test]
fn dot_completion_lists_only_interface_instance_methods() {
    let labels = completion_labels(
        r#"
def ShowInt : prop := struct
  show : int -> str
def show_int (n : int) : str := "n"
instance showInt : ShowInt := ShowInt.mk show_int
def free (n : int) : str := "free"
def n : int := 1
#eval n.<|>
"#,
    );

    assert!(labels.contains(&"show".to_string()), "{labels:?}");
    assert!(!labels.contains(&"show_int".to_string()), "{labels:?}");
    assert!(!labels.contains(&"free".to_string()), "{labels:?}");
}

#[test]
fn keyword_completion_and_constraint_relevance_are_sorted() {
    let labels = completion_labels(
        r#"
def letValue : int := 1
def main : int := le<|>
"#,
    );

    assert!(labels.contains(&"let".to_string()), "{labels:?}");
    assert!(labels.contains(&"letValue".to_string()), "{labels:?}");
    assert_label_before(&labels, "letValue", "let");
}

#[test]
fn module_path_completion_returns_visible_path_segments() {
    let labels = completion_labels(
        r#"
use std::io::print
use std::<|>
"#,
    );

    assert!(labels.contains(&"io".to_string()), "{labels:?}");
    assert!(!labels.contains(&"print".to_string()), "{labels:?}");
}

#[test]
fn namespace_qualified_completion_lists_visible_functions() {
    let labels = completion_labels(
        r#"
namespace Ops { pub def inc (x : int) : int := x + 1 }
#eval Ops::<|>
"#,
    );

    assert!(labels.contains(&"inc".to_string()), "{labels:?}");
}

#[tokio::test]
async fn service_completion_uses_open_document_snapshot() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let (source, position) = source_and_position(
        r#"
def n : int := 1
def main : int := <|>
"#,
    );

    service.did_open(uri.clone(), Some(1), source).await;
    let labels: Vec<_> = service
        .completion(&uri, position)
        .await
        .into_iter()
        .map(|item| item.label)
        .collect();

    assert!(labels.contains(&"n".to_string()), "{labels:?}");
}

#[tokio::test]
async fn goto_definition_resolves_function_parameter() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let (source, position) = source_and_position(
        r#"
def add (x : int) (y : int) : int := x + <|>y
"#,
    );

    service.did_open(uri.clone(), Some(1), source.clone()).await;
    let definition = service
        .goto_definition(&uri, position)
        .await
        .expect("definition");
    let lsp::GotoDefinitionResponse::Scalar(location) = definition else {
        panic!("expected scalar definition");
    };

    assert_eq!(location.uri, uri);
    assert_eq!(range_text(&source, location.range), "y");
    assert_eq!(location.range.start.line, 1);
}

#[tokio::test]
async fn goto_definition_resolves_constructor_and_struct_projector() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let (source, some_position) = source_and_position(
        r#"
def Option : prop := enum
  | None
  | Some of (value : int)
def Point : prop := struct
  x : int
def opt : Option := <|>Some 1
def get (p : Point) : int := Point.x p
"#,
    );
    let x_position = source
        .find("Point.x")
        .map(|offset| offset_to_position(&source, offset + "Point.".len()))
        .unwrap();

    service.did_open(uri.clone(), Some(1), source.clone()).await;

    let some_definition = service
        .goto_definition(&uri, some_position)
        .await
        .expect("constructor definition");
    let lsp::GotoDefinitionResponse::Scalar(some_location) = some_definition else {
        panic!("expected scalar definition");
    };
    assert_eq!(some_location.uri, uri);
    assert_eq!(range_text(&source, some_location.range), "Some");

    let field_definition = service
        .goto_definition(&uri, x_position)
        .await
        .expect("field definition");
    let lsp::GotoDefinitionResponse::Scalar(field_location) = field_definition else {
        panic!("expected scalar definition");
    };
    assert_eq!(field_location.uri, uri);
    assert_eq!(range_text(&source, field_location.range), "x");
}

#[tokio::test]
async fn goto_definition_resolves_open_cross_module_import() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let main_uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let math_uri = lsp::Url::parse("file:///workspace/math.lig").unwrap();
    let math = "{- The answer. -}\npub def one : int := 1\n".to_string();
    let (main, position) = source_and_position(
        r#"
mod math
use math::one
pub def main : IO () := let _ := <|>one in ()
"#,
    );

    service
        .did_open(math_uri.clone(), Some(1), math.clone())
        .await;
    service.did_open(main_uri.clone(), Some(1), main).await;
    let definition = service
        .goto_definition(&main_uri, position)
        .await
        .expect("cross-module definition");
    let lsp::GotoDefinitionResponse::Scalar(location) = definition else {
        panic!("expected scalar definition");
    };

    assert_eq!(location.uri, math_uri);
    assert_eq!(range_text(&math, location.range), "one");
    assert_eq!(location.range.start.line, 1);
}

#[tokio::test]
async fn service_loads_dependency_file_from_disk_cache() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let root = std::env::temp_dir().join(format!(
        "ligare_lsp_dep_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&root).unwrap();
    let math_path = root.join("math.lig");
    let main_path = root.join("main.lig");
    let math = "pub def one : int := 1\n".to_string();
    std::fs::write(&math_path, &math).unwrap();
    let math_uri = lsp::Url::from_file_path(&math_path).unwrap();
    let main_uri = lsp::Url::from_file_path(&main_path).unwrap();
    let (main, position) = source_and_position(
        r#"
mod math
use math::one
#eval <|>one
"#,
    );

    service.did_open(main_uri.clone(), Some(1), main).await;
    let definition = service
        .goto_definition(&main_uri, position)
        .await
        .expect("disk dependency definition");
    let lsp::GotoDefinitionResponse::Scalar(location) = definition else {
        panic!("expected scalar definition");
    };

    assert_eq!(location.uri, math_uri);
    assert_eq!(range_text(&math, location.range), "one");
}

#[tokio::test]
async fn service_loads_package_dependency_file_from_manifest() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let root = std::env::temp_dir().join(format!(
        "ligare_lsp_pkg_{}_{}",
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
    let math = "{- Increment. -}\npub def inc (x : int) : int := x + 1\n".to_string();
    let math_path = util.join("src/math.lig");
    std::fs::write(&math_path, &math).unwrap();
    let main_path = root.join("src/main.lig");
    let math_uri = lsp::Url::from_file_path(&math_path).unwrap();
    let main_uri = lsp::Url::from_file_path(&main_path).unwrap();
    let (main, position) = source_and_position(
        r#"
use util::math::inc
pub def main : IO () := let _ := <|>inc 1 in ()
"#,
    );

    service.did_open(main_uri.clone(), Some(1), main).await;
    let definition = service
        .goto_definition(&main_uri, position)
        .await
        .expect("package dependency definition");
    let lsp::GotoDefinitionResponse::Scalar(location) = definition else {
        panic!("expected scalar definition");
    };

    assert_eq!(location.uri, math_uri);
    assert_eq!(range_text(&math, location.range), "inc");
}

#[tokio::test]
async fn service_resolves_qualified_std_path_without_use() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher.clone());
    let root = std::env::temp_dir().join(format!(
        "ligare_lsp_std_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let std_root = root.join("std");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::create_dir_all(std_root.join("src")).unwrap();
    std::fs::write(
        root.join("ligare.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\n\n[dependencies]\nstd = { path = \"std\" }\n",
    )
    .unwrap();
    std::fs::write(
        std_root.join("ligare.toml"),
        "[package]\nname = \"std\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    std::fs::write(std_root.join("src/main.lig"), "pub mod io\n").unwrap();
    let io = "pub def put_str : int := 1\n".to_string();
    let io_path = std_root.join("src/io.lig");
    std::fs::write(&io_path, &io).unwrap();
    let main_uri = lsp::Url::from_file_path(root.join("src/main.lig")).unwrap();
    let io_uri = lsp::Url::from_file_path(&io_path).unwrap();
    let (source, position) = source_and_position("#check std::io::<|>put_str : int\n");

    service.did_open(main_uri.clone(), Some(1), source).await;
    let definition = service
        .goto_definition(&main_uri, position)
        .await
        .expect("qualified std definition");
    let lsp::GotoDefinitionResponse::Scalar(location) = definition else {
        panic!("expected scalar definition");
    };
    let notifications = publisher.wait_for_notifications(1).await;
    let diagnostics = &notifications.last().unwrap().1;

    assert_eq!(location.uri, io_uri);
    assert_eq!(range_text(&io, location.range), "put_str");
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| !diagnostic.message.contains("unbound: std::io::put_str")),
        "{diagnostics:#?}"
    );
}

#[tokio::test]
async fn service_diagnostics_resolve_package_imports_from_manifest() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher.clone());
    let root = std::env::temp_dir().join(format!(
        "ligare_lsp_pkg_diag_{}_{}",
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
    std::fs::write(
        util.join("src/math.lig"),
        "pub def inc (x : int) : int := x + 1\n",
    )
    .unwrap();
    let main_uri = lsp::Url::from_file_path(root.join("src/main.lig")).unwrap();
    let source = "use util::math::inc\n#check inc 1 : int\n".to_string();

    service.did_open(main_uri, Some(1), source).await;
    let notifications = publisher.wait_for_notifications(1).await;
    let diagnostics = &notifications.last().unwrap().1;

    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| !diagnostic.message.contains("unbound: inc")),
        "{diagnostics:#?}"
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[tokio::test]
async fn service_diagnostics_resolve_std_namespace_methods_from_manifest() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher.clone());
    let root = std::env::temp_dir().join(format!(
        "ligare_lsp_std_method_{}_{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let std_root = root.join("std");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::create_dir_all(std_root.join("src/mem")).unwrap();
    std::fs::write(
        root.join("ligare.toml"),
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\nstd = { path = \"std\" }\n",
    )
    .unwrap();
    std::fs::write(
        std_root.join("ligare.toml"),
        "[package]\nname = \"std\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    std::fs::write(std_root.join("src/main.lig"), "pub mod mem\n").unwrap();
    std::fs::write(std_root.join("src/mem/mod.lig"), "pub mod list\n").unwrap();
    std::fs::write(
        std_root.join("src/mem/list.lig"),
        r#"
pub def List (T : prop) : prop := enum
  | Nil
  | Const of (head : T) (next : List T)

namespace List {
  pub def append {T : prop} (l : List T) (n : T) : List T := Const n l
}
"#,
    )
    .unwrap();
    let main_uri = lsp::Url::from_file_path(root.join("src/main.lig")).unwrap();
    let source = r#"
use std::mem::list::List

pub def main : IO () := do
  let list := Nil
  let list_ := list.append 1
  ()
"#
    .to_string();

    service.did_open(main_uri, Some(1), source).await;
    let notifications = publisher.wait_for_notifications(2).await;
    let diagnostics = &notifications.last().unwrap().1;

    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[tokio::test]
async fn service_completes_package_dependency_modules_from_manifest() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let root = std::env::temp_dir().join(format!(
        "ligare_lsp_pkg_completion_{}_{}",
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
    std::fs::write(util.join("src/main.lig"), "pub mod math\nmod hidden\n").unwrap();
    std::fs::write(
        util.join("src/math.lig"),
        "pub def inc (x : int) : int := x + 1\n",
    )
    .unwrap();
    std::fs::write(util.join("src/hidden.lig"), "pub def secret : int := 1\n").unwrap();
    let main_path = root.join("src/main.lig");
    let main_uri = lsp::Url::from_file_path(&main_path).unwrap();
    let (source, position) = source_and_position("use util::<|>\n");

    service.did_open(main_uri.clone(), Some(1), source).await;
    let labels: Vec<_> = service
        .completion(&main_uri, position)
        .await
        .into_iter()
        .map(|item| item.label)
        .collect();

    assert!(labels.contains(&"math".to_string()), "{labels:?}");
    assert!(!labels.contains(&"hidden".to_string()), "{labels:?}");
}

#[tokio::test]
async fn hover_contains_constraint_and_doc_comment() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let main_uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let math_uri = lsp::Url::parse("file:///workspace/math.lig").unwrap();
    let math = "{- The answer. -}\npub def one : int := 1\n".to_string();
    let (main, position) = source_and_position(
        r#"
mod math
use math::one
pub def main : IO () := let _ := <|>one in ()
"#,
    );

    service.did_open(math_uri, Some(1), math).await;
    service.did_open(main_uri.clone(), Some(1), main).await;
    let hover = service.hover(&main_uri, position).await.expect("hover");
    let markdown = hover_markdown(hover);

    assert!(markdown.contains("one : int"), "{markdown}");
    assert!(markdown.contains("The answer."), "{markdown}");
}

#[tokio::test]
async fn hover_ignores_top_level_doc_comment_for_definition() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let (source, position) = source_and_position(
        r#"
{-! Module docs. -}
pub def one : int := 1
pub def main : int := <|>one
"#,
    );

    service.did_open(uri.clone(), Some(1), source).await;
    let hover = service.hover(&uri, position).await.expect("hover");
    let markdown = hover_markdown(hover);

    assert!(markdown.contains("one : int"), "{markdown}");
    assert!(!markdown.contains("Module docs."), "{markdown}");
}

#[tokio::test]
async fn goto_definition_resolves_module_declaration() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let (source, position) = source_and_position("mod <|>math\n");

    service.did_open(uri.clone(), Some(1), source.clone()).await;
    let definition = service
        .goto_definition(&uri, position)
        .await
        .expect("module definition");
    let lsp::GotoDefinitionResponse::Scalar(location) = definition else {
        panic!("expected scalar definition");
    };

    assert_eq!(location.uri, uri);
    assert_eq!(range_text(&source, location.range), "math");
}
