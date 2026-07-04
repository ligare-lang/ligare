use tower_lsp::lsp_types as lsp;

use super::{MOD_DEFINITION, MOD_PUBLIC, SemanticKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DecodedSemanticToken {
    pub(crate) text: String,
    pub(crate) kind: &'static str,
    pub(crate) modifiers: Vec<&'static str>,
}

pub(crate) fn decode_semantic_tokens(
    source: &str,
    tokens: &[lsp::SemanticToken],
) -> Vec<DecodedSemanticToken> {
    let mut line = 0;
    let mut character = 0;
    tokens
        .iter()
        .filter_map(|token| {
            line += token.delta_line;
            character = if token.delta_line == 0 {
                character + token.delta_start
            } else {
                token.delta_start
            };
            let start =
                crate::document::position_to_offset(source, lsp::Position { line, character })?;
            let end = crate::document::position_to_offset(
                source,
                lsp::Position {
                    line,
                    character: character + token.length,
                },
            )?;
            Some(DecodedSemanticToken {
                text: source[start..end].to_string(),
                kind: token_kind_name(token.token_type),
                modifiers: token_modifiers(token.token_modifiers_bitset),
            })
        })
        .collect()
}

fn token_kind_name(idx: u32) -> &'static str {
    match idx {
        0 => SemanticKind::Function.as_str(),
        1 => SemanticKind::Variable.as_str(),
        2 => SemanticKind::Constructor.as_str(),
        3 => SemanticKind::Constraint.as_str(),
        4 => SemanticKind::Namespace.as_str(),
        5 => SemanticKind::Keyword.as_str(),
        6 => SemanticKind::Parameter.as_str(),
        7 => SemanticKind::Comment.as_str(),
        8 => SemanticKind::Attribute.as_str(),
        _ => "unknown",
    }
}

fn token_modifiers(bitset: u32) -> Vec<&'static str> {
    let mut modifiers = Vec::new();
    if bitset & MOD_DEFINITION != 0 {
        modifiers.push("definition");
    }
    if bitset & MOD_PUBLIC != 0 {
        modifiers.push("public");
    }
    modifiers
}
