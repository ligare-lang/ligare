use std::collections::HashMap;
use std::ops::Range;

use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::config::BUILTIN_UNIT;
use ligare::front::lexer::Token;
use ligare::front::parser::TopLevel;
use tower_lsp::lsp_types as lsp;

use super::{RawSemanticToken, SemanticKind, SemanticModel, TokenSpan};
use crate::Ast;
use crate::document::offset_to_position;
use crate::semantic::classify::{
    dotted_kind, is_attribute_path_token, is_keyword, is_use_path_token, qualified_path_kind,
};

pub(super) fn collect_raw_tokens(
    source: &str,
    _ast: &Ast<'_>,
    _top_ranges: &[(usize, usize, TopLevel<'_>)],
    tokens: &[TokenSpan],
    model: &SemanticModel,
) -> Vec<RawSemanticToken> {
    let mut raw = comment_tokens(source);
    for (idx, token) in tokens.iter().enumerate() {
        if is_unit_builtin_token(tokens, idx) {
            raw.push(RawSemanticToken {
                span: token.span.start..tokens[idx + 1].span.end,
                kind: SemanticKind::Constraint,
                modifiers: 0,
                priority: 5,
            });
            continue;
        }

        if is_builtin_constraint_keyword(source, tokens, idx) {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind: SemanticKind::Constraint,
                modifiers: 0,
                priority: 5,
            });
            continue;
        }

        if is_keyword(&token.token) {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind: SemanticKind::Keyword,
                modifiers: 0,
                priority: 1,
            });
        }

        let Token::Ident(name) = &token.token else {
            continue;
        };

        if is_quote_keyword(tokens, idx) {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind: SemanticKind::Keyword,
                modifiers: 0,
                priority: 5,
            });
            continue;
        }

        if is_attribute_path_token(tokens, idx) {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind: SemanticKind::Attribute,
                modifiers: 0,
                priority: 10,
            });
            continue;
        }

        if let Some((kind, modifiers)) = model.declarations.get(&token.span.start) {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind: *kind,
                modifiers: *modifiers,
                priority: 10,
            });
            continue;
        }

        let kind = if let Some(kind) = qualified_path_kind(tokens, idx, model) {
            Some(kind)
        } else if is_use_path_token(tokens, idx) {
            Some(SemanticKind::Namespace)
        } else if let Some(kind) = dotted_kind(tokens, idx, model) {
            Some(kind)
        } else {
            model
                .local_kind_at(name, token.span.start)
                .or_else(|| model.global_kind(name))
        };

        if let Some(kind) = kind {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind,
                modifiers: 0,
                priority: 5,
            });
        } else if source[token.span.clone()].chars().next().is_some() {
            // Unknown identifiers intentionally remain unmarked.
        }
    }
    raw
}

fn is_unit_builtin_token(tokens: &[TokenSpan], idx: usize) -> bool {
    tokens
        .get(idx)
        .is_some_and(|token| token.token == Token::LParen)
        && tokens
            .get(idx + 1)
            .is_some_and(|token| token.token == Token::RParen)
        && BUILTIN_CONSTRAINT_NAMES.contains(&BUILTIN_UNIT)
}

fn is_builtin_constraint_keyword(source: &str, tokens: &[TokenSpan], idx: usize) -> bool {
    let Some(token) = tokens.get(idx) else {
        return false;
    };
    token.token == Token::KwTheorem && !is_theorem_declaration_token(source, tokens, idx)
}

fn is_quote_keyword(tokens: &[TokenSpan], idx: usize) -> bool {
    matches!(
        tokens.get(idx),
        Some(TokenSpan {
            token: Token::Ident(name),
            ..
        }) if name == "quote"
    ) && tokens
        .get(idx + 1)
        .is_some_and(|token| token.token == Token::LBrace)
}

fn is_theorem_declaration_token(source: &str, tokens: &[TokenSpan], idx: usize) -> bool {
    let Some(token) = tokens.get(idx) else {
        return false;
    };
    if is_line_start(source, token.span.start) {
        return true;
    }
    previous_non_newline(tokens, idx)
        .is_some_and(|prev| prev.token == Token::KwPub && is_line_start(source, prev.span.start))
}

fn previous_non_newline(tokens: &[TokenSpan], idx: usize) -> Option<&TokenSpan> {
    tokens[..idx]
        .iter()
        .rev()
        .find(|token| token.token != Token::Newline)
}

fn is_line_start(source: &str, offset: usize) -> bool {
    source[..offset]
        .rsplit_once('\n')
        .map_or(offset == 0, |(_, line)| line.trim().is_empty())
}

fn comment_tokens(source: &str) -> Vec<RawSemanticToken> {
    let mut raw = Vec::new();
    let bytes = source.as_bytes();
    let mut index = 0;

    while index < bytes.len() {
        if starts_with(bytes, index, b"--") {
            let start = index;
            index += 2;
            while index < bytes.len() && bytes[index] != b'\n' {
                index += 1;
            }
            push_comment_span(source, start..index, &mut raw);
        } else if starts_with(bytes, index, b"{-") {
            let start = index;
            index = scan_block_comment(bytes, index + 2, b'-', b'}');
            push_comment_span(source, start..index, &mut raw);
        } else if starts_with(bytes, index, b"/-") {
            let start = index;
            index = scan_nestable_block_comment(bytes, index + 2);
            push_comment_span(source, start..index, &mut raw);
        } else if bytes[index] == b'"' {
            index = scan_string(bytes, index + 1);
        } else {
            index += 1;
        }
    }

    raw
}

fn starts_with(bytes: &[u8], index: usize, needle: &[u8]) -> bool {
    bytes
        .get(index..index + needle.len())
        .is_some_and(|slice| slice == needle)
}

fn scan_block_comment(bytes: &[u8], mut index: usize, close_first: u8, close_second: u8) -> usize {
    while index + 1 < bytes.len() {
        if bytes[index] == close_first && bytes[index + 1] == close_second {
            return index + 2;
        }
        index += 1;
    }
    bytes.len()
}

fn scan_nestable_block_comment(bytes: &[u8], mut index: usize) -> usize {
    let mut depth = 1u32;
    while index + 1 < bytes.len() {
        if bytes[index] == b'/' && bytes[index + 1] == b'-' {
            depth += 1;
            index += 2;
        } else if bytes[index] == b'-' && bytes[index + 1] == b'/' {
            depth -= 1;
            index += 2;
            if depth == 0 {
                return index;
            }
        } else {
            index += 1;
        }
    }
    bytes.len()
}

fn scan_string(bytes: &[u8], mut index: usize) -> usize {
    while index < bytes.len() {
        if bytes[index] == b'\\' {
            index = (index + 2).min(bytes.len());
        } else if bytes[index] == b'"' {
            return index + 1;
        } else {
            index += 1;
        }
    }
    bytes.len()
}

fn push_comment_span(source: &str, span: Range<usize>, raw: &mut Vec<RawSemanticToken>) {
    let mut start = span.start;
    while start < span.end {
        let line_end = source[start..span.end]
            .find('\n')
            .map_or(span.end, |relative| start + relative);
        let token_end = if line_end > start && source.as_bytes()[line_end - 1] == b'\r' {
            line_end - 1
        } else {
            line_end
        };
        if start < token_end {
            raw.push(RawSemanticToken {
                span: start..token_end,
                kind: SemanticKind::Comment,
                modifiers: 0,
                priority: 20,
            });
        }
        if line_end == span.end {
            break;
        }
        start = line_end + 1;
    }
}

pub(super) fn encode_tokens(source: &str, raw: Vec<RawSemanticToken>) -> Vec<lsp::SemanticToken> {
    let mut by_start = HashMap::<usize, RawSemanticToken>::new();
    for token in raw {
        if token.span.is_empty() {
            continue;
        }
        match by_start.get(&token.span.start) {
            Some(existing) if existing.priority > token.priority => {}
            _ => {
                by_start.insert(token.span.start, token);
            }
        }
    }

    let mut positioned = by_start
        .into_values()
        .filter_map(|token| {
            let start = offset_to_position(source, token.span.start);
            let end = offset_to_position(source, token.span.end);
            (start.line == end.line && end.character >= start.character).then_some((
                start.line,
                start.character,
                end.character - start.character,
                token.kind,
                token.modifiers,
            ))
        })
        .collect::<Vec<_>>();
    positioned.sort_by_key(|(line, character, _, _, _)| (*line, *character));

    let mut previous_line = 0;
    let mut previous_start = 0;
    positioned
        .into_iter()
        .map(|(line, start, length, kind, modifiers)| {
            let delta_line = line - previous_line;
            let delta_start = if delta_line == 0 {
                start - previous_start
            } else {
                start
            };
            previous_line = line;
            previous_start = start;
            lsp::SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type: kind.token_type(),
                token_modifiers_bitset: modifiers,
            }
        })
        .collect()
}
