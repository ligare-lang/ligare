use super::*;

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
async fn document_symbols_list_top_level_symbols() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def Option : prop := enum
  | None
  | Some of (value : int)
def inc (x : int) : int := x + 1
"#
    .to_string();

    service.did_open(uri.clone(), Some(1), source).await;
    let symbols = service.document_symbols(&uri).await.expect("symbols");
    let lsp::DocumentSymbolResponse::Flat(symbols) = symbols else {
        panic!("expected flat document symbols");
    };
    let names = symbols
        .into_iter()
        .map(|symbol| symbol.name)
        .collect::<Vec<_>>();

    assert!(names.contains(&"Option".to_string()), "{names:?}");
    assert!(names.contains(&"Some".to_string()), "{names:?}");
    assert!(names.contains(&"inc".to_string()), "{names:?}");
}

#[tokio::test]
async fn references_find_local_symbol_uses() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let (source, position) = source_and_position(
        r#"
def n : int := 1
def a : int := <|>n
def b : int := n + n
"#,
    );

    service.did_open(uri.clone(), Some(1), source.clone()).await;
    let refs = service
        .references(&uri, position, true)
        .await
        .expect("references");
    let texts = refs
        .into_iter()
        .map(|location| range_text(&source, location.range).to_string())
        .collect::<Vec<_>>();

    assert_eq!(texts, vec!["n", "n", "n", "n"]);
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
