use super::*;

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
fn diagnostic_range_targets_unbound_identifier() {
    let source = "def good : int := 1\ndef bad : int := missing + good\n";
    let diagnostics = lsp_diagnostics_for_source(source, DiagnosticCheck::Fast);
    let diagnostic = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.message.contains("unbound: missing"))
        .expect("unbound diagnostic");

    assert_eq!(range_text(source, diagnostic.range), "missing");
}

#[test]
fn naming_warnings_use_warning_severity_and_name_ranges() {
    let source = "def bad_type : prop := enum\n  | One\ndef BadValue : int := 1\ntheorem BadTheorem : int := 0\n";
    let diagnostics = lsp_diagnostics_for_source(source, DiagnosticCheck::Fast);

    let type_warning = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.message.contains("constraint/type `bad_type`"))
        .expect("type naming warning");
    assert_eq!(
        type_warning.severity,
        Some(lsp::DiagnosticSeverity::WARNING)
    );
    assert_eq!(range_text(source, type_warning.range), "bad_type");

    let value_warning = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.message.contains("definition `BadValue`"))
        .expect("value naming warning");
    assert_eq!(
        value_warning.severity,
        Some(lsp::DiagnosticSeverity::WARNING)
    );
    assert_eq!(range_text(source, value_warning.range), "BadValue");

    let theorem_warning = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.message.contains("theorem `BadTheorem`"))
        .expect("theorem naming warning");
    assert_eq!(
        theorem_warning.severity,
        Some(lsp::DiagnosticSeverity::WARNING)
    );
    assert_eq!(range_text(source, theorem_warning.range), "BadTheorem");
}

#[tokio::test]
async fn service_publishes_naming_warnings() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher.clone());
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "def BadValue : int := 1\n";

    service.did_open(uri, Some(1), source.to_string()).await;

    let notifications = publisher.wait_for_notifications(1).await;
    let diagnostics = &notifications.last().unwrap().1;
    let warning = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.message.contains("definition `BadValue`"))
        .expect("naming warning");

    assert_eq!(warning.severity, Some(lsp::DiagnosticSeverity::WARNING));
    assert_eq!(range_text(source, warning.range), "BadValue");
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
