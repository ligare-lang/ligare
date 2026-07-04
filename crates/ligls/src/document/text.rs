use std::ops::Range;

use tower_lsp::lsp_types as lsp;

pub(crate) fn offset_to_position(source: &str, offset: usize) -> lsp::Position {
    let offset = offset.min(source.len());
    let mut line = 0u32;
    let mut line_start = 0usize;
    for (idx, ch) in source.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            line_start = idx + ch.len_utf8();
        }
    }

    let character = source[line_start..offset]
        .chars()
        .map(|ch| ch.len_utf16() as u32)
        .sum();
    lsp::Position { line, character }
}

pub(crate) fn apply_content_changes(
    mut text: String,
    changes: Vec<lsp::TextDocumentContentChangeEvent>,
) -> String {
    for change in changes {
        if let Some(range) = change.range {
            if let Some(byte_range) = lsp_range_to_byte_range(&text, range) {
                text.replace_range(byte_range, &change.text);
            } else {
                text = change.text;
            }
        } else {
            text = change.text;
        }
    }
    text
}

fn lsp_range_to_byte_range(source: &str, range: lsp::Range) -> Option<Range<usize>> {
    let start = position_to_offset(source, range.start)?;
    let end = position_to_offset(source, range.end)?;
    (start <= end).then_some(start..end)
}

pub(crate) fn position_to_offset(source: &str, position: lsp::Position) -> Option<usize> {
    let mut current_line = 0u32;
    let mut line_start = 0usize;
    for (idx, ch) in source.char_indices() {
        if current_line == position.line {
            break;
        }
        if ch == '\n' {
            current_line += 1;
            line_start = idx + ch.len_utf8();
        }
    }
    if current_line != position.line {
        return None;
    }

    let mut utf16 = 0u32;
    for (relative_idx, ch) in source[line_start..].char_indices() {
        if ch == '\n' {
            break;
        }
        if utf16 == position.character {
            return Some(line_start + relative_idx);
        }
        utf16 += ch.len_utf16() as u32;
        if utf16 > position.character {
            return None;
        }
    }
    if utf16 == position.character {
        Some(
            source[line_start..]
                .find('\n')
                .map_or(source.len(), |idx| line_start + idx),
        )
    } else {
        None
    }
}
