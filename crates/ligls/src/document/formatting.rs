use ligare::format::format_source;
use tower_lsp::lsp_types as lsp;

use super::text::offset_to_position;

pub fn formatting_edits(source: &str) -> Option<Vec<lsp::TextEdit>> {
    let formatted = format_source(source).ok()?;
    if formatted == source {
        return Some(Vec::new());
    }
    Some(vec![lsp::TextEdit {
        range: lsp::Range {
            start: lsp::Position {
                line: 0,
                character: 0,
            },
            end: offset_to_position(source, source.len()),
        },
        new_text: formatted,
    }])
}
