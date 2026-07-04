use std::collections::{HashMap, HashSet};
use std::ops::Range;

use ligare::front::parser::TopLevel;
use tower_lsp::lsp_types as lsp;

use crate::completion::{TokenSpan, expanded_top_level_ranges, tokenize};
use crate::{Ast, parse_program_lsp};

mod classify;
mod model;
#[cfg(test)]
mod test_support;
mod tokens;

use self::tokens::{collect_raw_tokens, encode_tokens};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SemanticKind {
    Function,
    Variable,
    Constructor,
    Constraint,
    Namespace,
    Keyword,
    Parameter,
    Comment,
    Attribute,
}

impl SemanticKind {
    #[cfg(test)]
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            SemanticKind::Function => "function",
            SemanticKind::Variable => "variable",
            SemanticKind::Constructor => "constructor",
            SemanticKind::Constraint => "constraint",
            SemanticKind::Namespace => "namespace",
            SemanticKind::Keyword => "keyword",
            SemanticKind::Parameter => "parameter",
            SemanticKind::Comment => "comment",
            SemanticKind::Attribute => "attribute",
        }
    }

    pub(crate) fn token_type(self) -> u32 {
        match self {
            SemanticKind::Function => 0,
            SemanticKind::Variable => 1,
            SemanticKind::Constructor => 2,
            SemanticKind::Constraint => 3,
            SemanticKind::Namespace => 4,
            SemanticKind::Keyword => 5,
            SemanticKind::Parameter => 6,
            SemanticKind::Comment => 7,
            SemanticKind::Attribute => 8,
        }
    }
}

pub(crate) const MOD_DEFINITION: u32 = 1 << 0;
pub(crate) const MOD_PUBLIC: u32 = 1 << 1;

pub fn semantic_tokens_legend() -> lsp::SemanticTokensLegend {
    lsp::SemanticTokensLegend {
        token_types: vec![
            lsp::SemanticTokenType::FUNCTION,
            lsp::SemanticTokenType::VARIABLE,
            lsp::SemanticTokenType::new("constructor"),
            lsp::SemanticTokenType::TYPE,
            lsp::SemanticTokenType::NAMESPACE,
            lsp::SemanticTokenType::KEYWORD,
            lsp::SemanticTokenType::PARAMETER,
            lsp::SemanticTokenType::COMMENT,
            lsp::SemanticTokenType::DECORATOR,
        ],
        token_modifiers: vec![
            lsp::SemanticTokenModifier::DEFINITION,
            lsp::SemanticTokenModifier::new("public"),
        ],
    }
}

pub(crate) fn semantic_tokens_for_source<'bump>(
    source: &str,
    ast: &Ast<'bump>,
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
) -> Vec<lsp::SemanticToken> {
    let tokens = tokenize(source);
    let model = SemanticModel::build(top_ranges, &tokens);
    encode_tokens(
        source,
        collect_raw_tokens(source, ast, top_ranges, &tokens, &model),
    )
}

pub fn semantic_tokens_for_source_text(source: &str) -> lsp::SemanticTokens {
    let bump = bumpalo::Bump::new();
    let arena = ligare::core::pool::TermArena::new(&bump);
    let (ast, _) = parse_program_lsp(source, &bump, &arena);
    let top_ranges = expanded_top_level_ranges(source, &ast, &bump, &arena);
    lsp::SemanticTokens {
        result_id: None,
        data: semantic_tokens_for_source(source, &ast, &top_ranges),
    }
}

#[derive(Debug, Clone)]
struct RawSemanticToken {
    span: Range<usize>,
    kind: SemanticKind,
    modifiers: u32,
    priority: u8,
}

#[derive(Debug, Default)]
struct SemanticModel {
    functions: HashSet<String>,
    variables: HashSet<String>,
    constructors: HashSet<String>,
    constraints: HashSet<String>,
    namespaces: HashSet<String>,
    declarations: HashMap<usize, (SemanticKind, u32)>,
    locals: Vec<LocalScope>,
}

#[derive(Debug)]
struct LocalScope {
    range: Range<usize>,
    constraints: HashSet<String>,
    params: HashSet<String>,
    variables: HashSet<String>,
}

#[cfg(test)]
pub(crate) use self::test_support::{DecodedSemanticToken, decode_semantic_tokens};
