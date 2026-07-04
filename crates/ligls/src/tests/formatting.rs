use super::*;

#[test]
fn formatting_edits_replace_whole_document() {
    let source = "pub def main:IO ():=\ndo\nlet x:int=5\nlet y:=x+1\ny\n";

    let edits = formatting_edits(source).expect("formatting edits");

    assert_eq!(edits.len(), 1);
    assert_eq!(
        edits[0].range,
        lsp::Range {
            start: lsp::Position {
                line: 0,
                character: 0
            },
            end: offset_to_position(source, source.len()),
        }
    );
    assert_eq!(
        edits[0].new_text,
        "pub def main : IO () :=\n  do\n    let x : int := 5\n    let y := x + 1\n    y\n"
    );
}

#[test]
fn formatting_edits_return_empty_when_source_is_stable() {
    let source = "pub def main : IO () := ()\n";

    let edits = formatting_edits(source).expect("formatting edits");

    assert!(edits.is_empty(), "{edits:#?}");
}

#[test]
fn formatting_edits_return_none_for_invalid_source() {
    assert!(formatting_edits("def broken : int := if true then\n").is_none());
}

#[tokio::test]
async fn service_formatting_uses_open_document_snapshot() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "pub def main:IO ():=do\nlet x:int=5\nx\n".to_string();

    service.did_open(uri.clone(), Some(1), source).await;
    let edits = service.formatting(&uri).await.expect("formatting");

    assert_eq!(edits.len(), 1);
    assert_eq!(
        edits[0].new_text,
        "pub def main : IO () :=\n  do\n    let x : int := 5\n    x\n"
    );
}

#[tokio::test]
async fn service_formatting_returns_none_for_invalid_snapshot() {
    let publisher = RecordingPublisher::default();
    let service = DiagnosticService::new(publisher);
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "def broken : int := if true then\n".to_string();

    service.did_open(uri.clone(), Some(1), source).await;

    assert!(service.formatting(&uri).await.is_none());
}
