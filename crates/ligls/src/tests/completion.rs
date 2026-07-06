use super::*;

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
#[instance]
def showInt : ShowInt := ShowInt.mk show_int
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
fn completion_includes_metaprogramming_symbols() {
    let labels = completion_labels("#check <|>");

    assert!(labels.contains(&"quote".to_string()), "{labels:?}");
    assert!(labels.contains(&"Expr".to_string()), "{labels:?}");
    assert!(labels.contains(&"Int".to_string()), "{labels:?}");
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
