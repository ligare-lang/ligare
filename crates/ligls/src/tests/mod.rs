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
use crate::document::{offset_to_position, position_to_offset};
use crate::semantic::decode_semantic_tokens;
use crate::{
    AstNode, DiagnosticCheck, DiagnosticPublisher, DiagnosticService, completion_items_for_source,
    formatting_edits, lsp_diagnostics_for_source, parse_program_lsp,
};

mod cache;
mod completion;
mod diagnostics;
mod formatting;
mod navigation;
mod parser;
mod semantic;

fn arena() -> (&'static Bump, TermArena<'static>) {
    let bump = Box::leak(Box::new(Bump::new()));
    (bump, TermArena::new(bump))
}

type PublishedDiagnostics = Arc<Mutex<Vec<(lsp::Url, Vec<lsp::Diagnostic>, Option<i32>)>>>;

#[derive(Clone, Default)]
struct RecordingPublisher {
    notifications: PublishedDiagnostics,
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
