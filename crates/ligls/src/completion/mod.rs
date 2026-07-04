use std::ops::Range;

use bumpalo::Bump;
use ligare::core::pool::TermArena;
use ligare::core::syntax::Term;
use ligare::front::lexer::Token;
use logos::Logos;
use tower_lsp::lsp_types as lsp;

use crate::document::position_to_offset;
use crate::parse_program_lsp;

mod collect;
mod context;
mod render;

use self::collect::{builtin_symbols, collect_module_paths, collect_symbols, keyword_symbols};
use self::context::build_context;
use self::render::{
    dot_candidates, module_path_candidates, normal_candidates, qualified_path_candidates,
    sort_and_dedup, symbol_to_completion,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SymbolKind {
    Local,
    Value,
    Function,
    Constructor,
    Type,
    Import,
    Module,
    Keyword,
}

impl SymbolKind {
    pub(crate) fn lsp_kind(self) -> lsp::CompletionItemKind {
        match self {
            SymbolKind::Local => lsp::CompletionItemKind::VARIABLE,
            SymbolKind::Value => lsp::CompletionItemKind::VALUE,
            SymbolKind::Function => lsp::CompletionItemKind::FUNCTION,
            SymbolKind::Constructor => lsp::CompletionItemKind::CONSTRUCTOR,
            SymbolKind::Type => lsp::CompletionItemKind::STRUCT,
            SymbolKind::Import | SymbolKind::Module => lsp::CompletionItemKind::MODULE,
            SymbolKind::Keyword => lsp::CompletionItemKind::KEYWORD,
        }
    }

    pub(crate) fn base_rank(self) -> u8 {
        match self {
            SymbolKind::Local => 0,
            SymbolKind::Value => 1,
            SymbolKind::Constructor => 2,
            SymbolKind::Function => 3,
            SymbolKind::Type => 4,
            SymbolKind::Import => 5,
            SymbolKind::Module => 6,
            SymbolKind::Keyword => 7,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Constraint {
    pub(crate) display: String,
    key: String,
}

impl Constraint {
    pub(crate) fn new(display: impl Into<String>) -> Self {
        let display = display.into();
        let key = normalize_constraint(&display);
        Self { display, key }
    }

    pub(crate) fn from_term(term: &Term<'_>) -> Self {
        Self::new(ligare::pretty::PrettyPrinter::pretty(term))
    }

    pub(crate) fn named(name: &str) -> Self {
        Self::new(name)
    }

    fn is_data_like(&self) -> bool {
        matches!(self.key.as_str(), "data")
    }

    pub(crate) fn matches_expected(&self, expected: &Constraint) -> bool {
        self.key == expected.key || expected.is_data_like()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Signature {
    pub(crate) whole: Constraint,
    pub(crate) params: Vec<Constraint>,
    pub(crate) result: Constraint,
}

#[derive(Debug, Clone)]
pub(crate) struct Symbol {
    pub(crate) name: String,
    pub(crate) detail: String,
    pub(crate) constraint: Option<Constraint>,
    pub(crate) signature: Option<Signature>,
    pub(crate) kind: SymbolKind,
    pub(crate) imported_path: Option<Vec<String>>,
}

#[derive(Debug, Clone)]
pub(crate) struct TokenSpan {
    pub(crate) token: Token,
    pub(crate) span: Range<usize>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CompletionMode {
    Normal,
    Dot,
    ModulePath,
    QualifiedPath,
}

#[derive(Debug, Clone)]
pub(crate) struct CompletionContext {
    pub(crate) prefix: String,
    pub(crate) mode: CompletionMode,
    pub(crate) expected: Option<Constraint>,
    pub(crate) receiver_constraint: Option<Constraint>,
    pub(crate) module_path_prefix: Vec<String>,
}

const KEYWORDS: &[&str] = &[
    "let",
    "in",
    "if",
    "then",
    "else",
    "true",
    "false",
    "by",
    "fun",
    "func",
    "do",
    "where",
    "def",
    "extern",
    "unsafe",
    "pure",
    "auto",
    "exact",
    "apply",
    "intro",
    "have",
    "theorem",
    "pub",
    "use",
    "mod",
    "namespace",
    "as",
    "struct",
    "enum",
    "match",
    "with",
    "of",
    "quote",
];

pub(crate) const META_EXPR_TYPE: &str = "Expr";
pub(crate) const META_EXPR_VARIANTS: &[&str] = &[
    "Int", "Bool", "Str", "Var", "Name", "Global", "Prim", "App", "Lam", "Let", "If", "Annot",
];

pub fn completion_items_for_source(
    source: &str,
    position: lsp::Position,
) -> Vec<lsp::CompletionItem> {
    completion_items_for_source_with_module_paths(source, position, Vec::new())
}

pub(crate) fn completion_items_for_source_with_module_paths(
    source: &str,
    position: lsp::Position,
    extra_module_paths: Vec<Vec<String>>,
) -> Vec<lsp::CompletionItem> {
    let Some(offset) = position_to_offset(source, position) else {
        return Vec::new();
    };
    completion_items_at_offset(source, offset, extra_module_paths)
}

fn completion_items_at_offset(
    source: &str,
    offset: usize,
    extra_module_paths: Vec<Vec<String>>,
) -> Vec<lsp::CompletionItem> {
    let bump = Bump::new();
    let arena = TermArena::new(&bump);
    let (ast, _) = parse_program_lsp(source, &bump, &arena);
    let tokens = tokenize(source);
    let top_ranges = expanded_top_level_ranges(source, &ast, &bump, &arena);
    let mut symbols = collect_symbols(source, &tokens, &top_ranges, offset);
    let mut module_paths = collect_module_paths(&symbols);
    module_paths.extend(extra_module_paths);
    module_paths.sort();
    module_paths.dedup();
    symbols.extend(keyword_symbols());
    symbols.extend(builtin_symbols());

    let context = build_context(source, offset, &tokens, &symbols, &top_ranges);
    let mut candidates = match context.mode {
        CompletionMode::Dot => dot_candidates(&symbols, &context),
        CompletionMode::ModulePath => module_path_candidates(&module_paths, &context),
        CompletionMode::QualifiedPath => qualified_path_candidates(&symbols, &context),
        CompletionMode::Normal => normal_candidates(&symbols, &context),
    };

    sort_and_dedup(&mut candidates, &context);
    candidates
        .into_iter()
        .map(|symbol| symbol_to_completion(symbol, &context))
        .collect()
}

pub(crate) fn tokenize(source: &str) -> Vec<TokenSpan> {
    Token::lexer(source)
        .spanned()
        .filter_map(|(result, span)| {
            result.ok().and_then(|token| {
                (token != Token::BlockComment).then_some(TokenSpan {
                    token,
                    span: span.clone(),
                })
            })
        })
        .collect()
}

pub(crate) fn constraint_from_source(source: &str, range: Range<usize>) -> Option<Constraint> {
    let text = source.get(range)?.trim();
    (!text.is_empty()).then(|| Constraint::new(text))
}

impl Symbol {
    pub(crate) fn value_constraint(&self) -> Option<Constraint> {
        if self
            .signature
            .as_ref()
            .is_some_and(|sig| !sig.params.is_empty())
        {
            return None;
        }
        self.signature
            .as_ref()
            .map(|sig| sig.result.clone())
            .or_else(|| self.constraint.clone())
    }

    pub(crate) fn satisfies_expected(&self, expected: &Constraint) -> bool {
        if self.kind == SymbolKind::Keyword || self.kind == SymbolKind::Module {
            return false;
        }
        if let Some(value) = self.value_constraint() {
            value.matches_expected(expected)
        } else {
            self.constraint
                .as_ref()
                .is_some_and(|constraint| constraint.matches_expected(expected))
        }
    }
}

fn normalize_constraint(input: &str) -> String {
    let mut out = String::new();
    let mut previous_space = false;
    for ch in input.trim().chars() {
        if ch.is_whitespace() {
            if !previous_space {
                out.push(' ');
                previous_space = true;
            }
        } else if matches!(ch, '(' | ')') {
            previous_space = false;
        } else {
            out.push(ch);
            previous_space = false;
        }
    }
    out
}

pub(crate) use self::collect::{
    collect_top_level_symbols, constructor_signature, expanded_top_level_ranges,
    infer_literal_constraint, signature_from_parts, term_signature, top_level_ranges, top_params,
    top_start, type_or_value_kind,
};
