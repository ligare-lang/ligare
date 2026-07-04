use std::cmp::Ordering;
use std::collections::HashSet;
use std::ops::Range;

use bumpalo::Bump;
use ligare::checker::CheckMode;
use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::core::syntax::{Name, Term};
use ligare::front::lexer::Token;
use ligare::front::parser::TopLevel;
use ligare::pretty::PrettyPrinter;
use logos::Logos;
use tower_lsp::lsp_types as lsp;

use crate::parse_program_lsp;
use crate::text::position_to_offset;

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

    fn base_rank(self) -> u8 {
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
        Self::new(PrettyPrinter::pretty(term))
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
enum CompletionMode {
    Normal,
    Dot,
    ModulePath,
    QualifiedPath,
}

#[derive(Debug, Clone)]
struct CompletionContext {
    prefix: String,
    mode: CompletionMode,
    expected: Option<Constraint>,
    receiver_constraint: Option<Constraint>,
    module_path_prefix: Vec<String>,
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

fn collect_symbols<'bump>(
    source: &str,
    tokens: &[TokenSpan],
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
    offset: usize,
) -> Vec<Symbol> {
    let mut symbols = Vec::new();
    for (_, _, top) in top_ranges {
        collect_top_level_symbols(top, &mut symbols);
    }
    symbols.extend(local_symbols(source, tokens, top_ranges, offset));
    symbols
}

pub(crate) fn collect_top_level_symbols(top: &TopLevel<'_>, symbols: &mut Vec<Symbol>) {
    match top {
        TopLevel::TLPublic(inner) => collect_top_level_symbols(inner, symbols),
        TopLevel::TLAttributed(_, inner, _) => collect_top_level_symbols(inner, symbols),
        TopLevel::TLDef(name, params, ret, body, _) => {
            let signature = if params.is_empty() {
                term_signature(body)
            } else {
                ret.map(|ret| signature_from_parts(params, ret))
                    .or_else(|| term_signature(body))
            };
            let constraint = signature
                .as_ref()
                .map(|sig| sig.whole.clone())
                .or_else(|| ret.map(Constraint::from_term));
            let kind = if params.is_empty() {
                type_or_value_kind(body)
            } else {
                SymbolKind::Function
            };
            symbols.push(Symbol {
                name: (*name).to_string(),
                detail: constraint
                    .as_ref()
                    .map(|c| c.display.clone())
                    .unwrap_or_else(|| "data".to_string()),
                constraint,
                signature,
                kind,
                imported_path: None,
            });
            collect_type_members(name, body, symbols);
        }
        TopLevel::TLExternDef(name, params, ret, _) => {
            let signature = signature_from_parts(params, ret);
            symbols.push(Symbol {
                name: (*name).to_string(),
                detail: signature.whole.display.clone(),
                constraint: Some(signature.whole.clone()),
                signature: Some(signature),
                kind: SymbolKind::Function,
                imported_path: None,
            });
        }
        TopLevel::TLInstance(name, constraint, _, _) => symbols.push(Symbol {
            name: (*name).to_string(),
            detail: Constraint::from_term(constraint).display,
            constraint: Some(Constraint::from_term(constraint)),
            signature: None,
            kind: SymbolKind::Value,
            imported_path: None,
        }),
        TopLevel::TLVariable(_, _) => {}
        TopLevel::TLTheorem(name, prop, _, _) => symbols.push(Symbol {
            name: (*name).to_string(),
            detail: PrettyPrinter::pretty(prop),
            constraint: Some(Constraint::from_term(prop)),
            signature: None,
            kind: SymbolKind::Value,
            imported_path: None,
        }),
        TopLevel::TLUse(uses, _, _) => {
            for use_tree in *uses {
                let path: Vec<String> = use_tree
                    .path
                    .iter()
                    .map(|part| (*part).to_string())
                    .collect();
                let name = use_tree
                    .alias
                    .map(|alias| alias.to_string())
                    .or_else(|| path.last().cloned())
                    .unwrap_or_default();
                if !name.is_empty() {
                    symbols.push(Symbol {
                        name,
                        detail: format!("import {}", path.join("::")),
                        constraint: None,
                        signature: None,
                        kind: SymbolKind::Import,
                        imported_path: Some(path),
                    });
                }
            }
        }
        TopLevel::TLMod(name, _) => symbols.push(Symbol {
            name: (*name).to_string(),
            detail: "module".to_string(),
            constraint: None,
            signature: None,
            kind: SymbolKind::Module,
            imported_path: Some(vec![(*name).to_string()]),
        }),
        TopLevel::TLNamespace(name, items, _) => {
            for item in *items {
                collect_namespace_symbols(name, item, symbols);
            }
        }
        TopLevel::TLCheck(_, _, _)
        | TopLevel::TLEval(_, _)
        | TopLevel::TLExpr(_, _)
        | TopLevel::TLSplice(_, _) => {}
    }
}

fn collect_namespace_symbols(namespace: &str, top: &TopLevel<'_>, symbols: &mut Vec<Symbol>) {
    let before = symbols.len();
    collect_top_level_symbols(top, symbols);
    for symbol in symbols.iter_mut().skip(before) {
        if !symbol.name.contains("::") {
            symbol.name = format!("{namespace}::{}", symbol.name);
        }
    }
}

fn collect_type_members(type_name: &str, body: &Term<'_>, symbols: &mut Vec<Symbol>) {
    let inner = match body {
        Term::Annot(inner, _) => *inner,
        other => other,
    };
    match inner {
        Term::EnumDef(enum_name, variants) => {
            for (variant_name, fields) in *variants {
                let signature = constructor_signature(enum_name, fields);
                symbols.push(Symbol {
                    name: (*variant_name).to_string(),
                    detail: signature
                        .as_ref()
                        .map(|sig| sig.whole.display.clone())
                        .unwrap_or_else(|| enum_name.to_string()),
                    constraint: signature
                        .as_ref()
                        .map(|sig| sig.whole.clone())
                        .or_else(|| Some(Constraint::named(enum_name))),
                    signature,
                    kind: SymbolKind::Constructor,
                    imported_path: None,
                });
            }
        }
        Term::StructDef(struct_name, fields) => {
            let ctor_signature = constructor_signature(struct_name, fields);
            symbols.push(Symbol {
                name: format!("{type_name}.mk"),
                detail: ctor_signature
                    .as_ref()
                    .map(|sig| sig.whole.display.clone())
                    .unwrap_or_else(|| struct_name.to_string()),
                constraint: ctor_signature
                    .as_ref()
                    .map(|sig| sig.whole.clone())
                    .or_else(|| Some(Constraint::named(struct_name))),
                signature: ctor_signature,
                kind: SymbolKind::Constructor,
                imported_path: None,
            });
            for (field_name, field_constraint) in *fields {
                let whole = Constraint::new(format!(
                    "({} -> {})",
                    struct_name,
                    PrettyPrinter::pretty(field_constraint)
                ));
                symbols.push(Symbol {
                    name: format!("{type_name}.{field_name}"),
                    detail: whole.display.clone(),
                    constraint: Some(whole.clone()),
                    signature: Some(Signature {
                        whole,
                        params: vec![Constraint::named(struct_name)],
                        result: Constraint::from_term(field_constraint),
                    }),
                    kind: SymbolKind::Function,
                    imported_path: None,
                });
            }
        }
        _ => {}
    }
}

pub(crate) fn constructor_signature(
    result_name: &str,
    fields: &[(Name<'_>, &Term<'_>)],
) -> Option<Signature> {
    if fields.is_empty() {
        return None;
    }
    let params: Vec<_> = fields
        .iter()
        .map(|(_, constraint)| Constraint::from_term(constraint))
        .collect();
    let result = Constraint::named(result_name);
    let display = params
        .iter()
        .rev()
        .fold(result.display.clone(), |acc, param| {
            format!("({} -> {})", param.display, acc)
        });
    Some(Signature {
        whole: Constraint::new(display),
        params,
        result,
    })
}

pub(crate) fn term_signature(term: &Term<'_>) -> Option<Signature> {
    match term {
        Term::Annot(_, constraint) => Some(signature_from_constraint(constraint)),
        _ => None,
    }
}

pub(crate) fn signature_from_parts(
    params: &[(Name<'_>, Option<&Term<'_>>)],
    ret: &Term<'_>,
) -> Signature {
    let mut constraints = Vec::new();
    for (_, constraint) in params {
        constraints.push(
            constraint
                .map(Constraint::from_term)
                .unwrap_or_else(|| Constraint::named("data")),
        );
    }
    let result = Constraint::from_term(ret);
    let whole = constraints
        .iter()
        .rev()
        .fold(result.display.clone(), |acc, param| {
            format!("({} -> {})", param.display, acc)
        });
    Signature {
        whole: Constraint::new(whole),
        params: constraints,
        result,
    }
}

fn signature_from_constraint(term: &Term<'_>) -> Signature {
    let mut params = Vec::new();
    let mut current = term;
    while let Term::Pi(_, domain, codomain) = current {
        params.push(Constraint::from_term(domain));
        current = codomain;
    }
    Signature {
        whole: Constraint::from_term(term),
        params,
        result: Constraint::from_term(current),
    }
}

pub(crate) fn type_or_value_kind(term: &Term<'_>) -> SymbolKind {
    match term {
        Term::Annot(Term::EnumDef(..) | Term::StructDef(..), _) => SymbolKind::Type,
        _ => SymbolKind::Value,
    }
}

fn local_symbols<'bump>(
    source: &str,
    tokens: &[TokenSpan],
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
    offset: usize,
) -> Vec<Symbol> {
    let mut locals = Vec::new();
    if let Some((start, _, top)) = top_ranges
        .iter()
        .find(|(start, end, _)| *start <= offset && offset <= *end)
    {
        if let Some(params) = top_params(top) {
            for (name, constraint) in params {
                let constraint = constraint
                    .map(Constraint::from_term)
                    .unwrap_or_else(|| Constraint::named("data"));
                locals.push(Symbol {
                    name: (*name).to_string(),
                    detail: constraint.display.clone(),
                    constraint: Some(constraint),
                    signature: None,
                    kind: SymbolKind::Local,
                    imported_path: None,
                });
            }
        }
        collect_lexical_lets(source, tokens, *start, offset, &mut locals);
    }
    locals
}

pub(crate) fn top_params<'bump>(
    top: &TopLevel<'bump>,
) -> Option<&'bump [(Name<'bump>, Option<&'bump Term<'bump>>)]> {
    match top {
        TopLevel::TLPublic(inner) => top_params(inner),
        TopLevel::TLDef(_, params, _, _, _) | TopLevel::TLExternDef(_, params, _, _) => {
            Some(*params)
        }
        _ => None,
    }
}

fn collect_lexical_lets(
    source: &str,
    tokens: &[TokenSpan],
    start: usize,
    offset: usize,
    locals: &mut Vec<Symbol>,
) {
    let mut i = 0;
    while i + 1 < tokens.len() {
        let token = &tokens[i];
        if token.span.start < start || token.span.start >= offset {
            i += 1;
            continue;
        }
        if token.token != Token::KwLet {
            i += 1;
            continue;
        }
        let Some(TokenSpan {
            token: Token::Ident(name),
            span: name_span,
        }) = tokens.get(i + 1)
        else {
            i += 1;
            continue;
        };
        if name_span.start >= offset {
            i += 1;
            continue;
        }
        let mut constraint = None;
        let mut j = i + 2;
        if tokens.get(j).is_some_and(|t| t.token == Token::Colon) {
            let constraint_start = tokens[j].span.end;
            j += 1;
            while tokens.get(j).is_some_and(|t| {
                !matches!(
                    t.token,
                    Token::ColonEq | Token::Eq | Token::KwIn | Token::Semi
                )
            }) {
                j += 1;
            }
            if let Some(delim) = tokens.get(j) {
                constraint = constraint_from_source(source, constraint_start..delim.span.start);
            }
        }
        if constraint.is_none() {
            while tokens.get(j).is_some_and(|t| {
                !matches!(
                    t.token,
                    Token::ColonEq | Token::Eq | Token::KwIn | Token::Semi
                )
            }) {
                j += 1;
            }
            if tokens
                .get(j)
                .is_some_and(|t| matches!(t.token, Token::ColonEq | Token::Eq))
            {
                constraint = infer_literal_constraint(tokens.get(j + 1).map(|t| &t.token));
            }
        }
        let constraint = constraint.unwrap_or_else(|| Constraint::named("data"));
        locals.push(Symbol {
            name: name.clone(),
            detail: constraint.display.clone(),
            constraint: Some(constraint),
            signature: None,
            kind: SymbolKind::Local,
            imported_path: None,
        });
        i += 1;
    }
}

pub(crate) fn infer_literal_constraint(token: Option<&Token>) -> Option<Constraint> {
    match token {
        Some(Token::IntLit(_)) => Some(Constraint::named("int")),
        Some(Token::True | Token::False) => Some(Constraint::named("bool")),
        Some(Token::StrLit(_)) => Some(Constraint::named("str")),
        _ => None,
    }
}

fn keyword_symbols() -> Vec<Symbol> {
    KEYWORDS
        .iter()
        .map(|keyword| Symbol {
            name: (*keyword).to_string(),
            detail: "keyword".to_string(),
            constraint: None,
            signature: None,
            kind: SymbolKind::Keyword,
            imported_path: None,
        })
        .collect()
}

fn builtin_symbols() -> Vec<Symbol> {
    let mut symbols = BUILTIN_CONSTRAINT_NAMES
        .iter()
        .map(|name| Symbol {
            name: (*name).to_string(),
            detail: "builtin constraint".to_string(),
            constraint: Some(Constraint::named("prop")),
            signature: None,
            kind: SymbolKind::Type,
            imported_path: None,
        })
        .collect::<Vec<_>>();
    symbols.extend(meta_symbols());
    symbols
}

pub(crate) fn meta_symbols() -> Vec<Symbol> {
    let mut symbols = vec![Symbol {
        name: META_EXPR_TYPE.to_string(),
        detail: "builtin meta constraint".to_string(),
        constraint: Some(Constraint::named("prop")),
        signature: None,
        kind: SymbolKind::Type,
        imported_path: None,
    }];
    symbols.extend(META_EXPR_VARIANTS.iter().map(|variant| Symbol {
        name: (*variant).to_string(),
        detail: META_EXPR_TYPE.to_string(),
        constraint: Some(Constraint::named(META_EXPR_TYPE)),
        signature: None,
        kind: SymbolKind::Constructor,
        imported_path: None,
    }));
    symbols
}

fn build_context(
    source: &str,
    offset: usize,
    tokens: &[TokenSpan],
    symbols: &[Symbol],
    top_ranges: &[(usize, usize, TopLevel<'_>)],
) -> CompletionContext {
    let prefix_range = identifier_prefix_range(source, offset);
    let prefix = source[prefix_range.clone()].to_string();
    if let Some(path_prefix) = module_path_context(source, prefix_range.start) {
        return CompletionContext {
            prefix,
            mode: CompletionMode::ModulePath,
            expected: None,
            receiver_constraint: None,
            module_path_prefix: path_prefix,
        };
    }
    if let Some(path_prefix) = qualified_path_context(source, prefix_range.start) {
        return CompletionContext {
            prefix,
            mode: CompletionMode::QualifiedPath,
            expected: None,
            receiver_constraint: None,
            module_path_prefix: path_prefix,
        };
    }
    if let Some(receiver_text) = dot_receiver_text(source, prefix_range.start) {
        let receiver_constraint = infer_expr_constraint(receiver_text, symbols);
        return CompletionContext {
            prefix,
            mode: CompletionMode::Dot,
            expected: None,
            receiver_constraint,
            module_path_prefix: Vec::new(),
        };
    }
    let expected = expected_constraint(source, offset, tokens, symbols, top_ranges);
    CompletionContext {
        prefix,
        mode: CompletionMode::Normal,
        expected,
        receiver_constraint: None,
        module_path_prefix: Vec::new(),
    }
}

fn qualified_path_context(source: &str, prefix_start: usize) -> Option<Vec<String>> {
    let before = source[..prefix_start].trim_end();
    if !before.ends_with("::") {
        return None;
    }
    let path_end = before.len().saturating_sub(2);
    let path_start = source[..path_end]
        .rfind(|ch: char| {
            ch.is_whitespace()
                || matches!(
                    ch,
                    '(' | ')' | '{' | '}' | '[' | ']' | ',' | ';' | ':' | '=' | '<' | '>'
                )
        })
        .map_or(0, |idx| idx + 1);
    let path = source[path_start..path_end].trim();
    (!path.is_empty()).then(|| path.split("::").map(|part| part.to_string()).collect())
}

fn identifier_prefix_range(source: &str, offset: usize) -> Range<usize> {
    let offset = offset.min(source.len());
    let mut start = offset;
    while start > 0 {
        let Some((idx, ch)) = source[..start].char_indices().next_back() else {
            break;
        };
        if is_ident_continue(ch) {
            start = idx;
        } else {
            break;
        }
    }
    start..offset
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn module_path_context(source: &str, prefix_start: usize) -> Option<Vec<String>> {
    let line_start = source[..prefix_start].rfind('\n').map_or(0, |idx| idx + 1);
    let before = &source[line_start..prefix_start];
    if !before.trim_start().starts_with("use ") && !before.trim_start().starts_with("pub use ") {
        return None;
    }
    let path_start = before
        .rfind(|ch: char| ch.is_whitespace() || ch == ',' || ch == '{')
        .map_or(0, |idx| idx + 1);
    let path = before[path_start..].trim();
    if !path.contains("::") {
        return None;
    }
    Some(
        path.split("::")
            .filter(|segment| !segment.is_empty())
            .map(|segment| segment.to_string())
            .collect(),
    )
}

fn dot_receiver_text(source: &str, prefix_start: usize) -> Option<&str> {
    let before_prefix = source[..prefix_start].trim_end();
    if !before_prefix.ends_with('.') {
        return None;
    }
    let dot = before_prefix.len().saturating_sub(1);
    let receiver_end = dot;
    let receiver_start = source[..receiver_end]
        .rfind(|ch: char| {
            ch.is_whitespace()
                || matches!(
                    ch,
                    '(' | ')' | '{' | '}' | '[' | ']' | ',' | ';' | ':' | '=' | '<' | '>'
                )
        })
        .map_or(0, |idx| idx + 1);
    let text = source[receiver_start..receiver_end].trim();
    (!text.is_empty()).then_some(text)
}

fn infer_expr_constraint(expr: &str, symbols: &[Symbol]) -> Option<Constraint> {
    let expr = expr.trim();
    if expr.parse::<i64>().is_ok() {
        return Some(Constraint::named("int"));
    }
    if matches!(expr, "true" | "false") {
        return Some(Constraint::named("bool"));
    }
    if expr.starts_with('"') && expr.ends_with('"') {
        return Some(Constraint::named("str"));
    }
    symbols
        .iter()
        .find(|symbol| symbol.name == expr)
        .and_then(|symbol| symbol.value_constraint())
}

fn expected_constraint(
    source: &str,
    offset: usize,
    tokens: &[TokenSpan],
    symbols: &[Symbol],
    top_ranges: &[(usize, usize, TopLevel<'_>)],
) -> Option<Constraint> {
    check_directive_expected(source, offset, tokens)
        .or_else(|| assignment_expected(source, offset, tokens, top_ranges))
        .or_else(|| function_argument_expected(source, offset, tokens, symbols))
        .or_else(|| if_condition_expected(offset, tokens))
}

fn check_directive_expected(
    source: &str,
    offset: usize,
    tokens: &[TokenSpan],
) -> Option<Constraint> {
    let line_start = source[..offset].rfind('\n').map_or(0, |idx| idx + 1);
    let line_end = source[offset..]
        .find('\n')
        .map_or(source.len(), |idx| offset + idx);
    let line = &source[line_start..line_end];
    if !line.trim_start().starts_with("#check") {
        return None;
    }
    tokens
        .iter()
        .find(|token| {
            token.span.start >= line_start
                && token.span.end <= line_end
                && token.span.start > offset
                && token.token == Token::Colon
        })
        .and_then(|colon| constraint_from_source(source, colon.span.end..line_end))
}

fn assignment_expected<'bump>(
    source: &str,
    offset: usize,
    tokens: &[TokenSpan],
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
) -> Option<Constraint> {
    if let Some((start, _, top)) = top_ranges
        .iter()
        .find(|(start, end, _)| *start <= offset && offset <= *end)
        && let Some(assign) = last_token_before(tokens, offset, |t| t.token == Token::ColonEq)
        && assign.span.start >= *start
        && offset >= assign.span.end
    {
        if let Some(let_constraint) = let_assignment_constraint(source, tokens, assign.span.start) {
            return Some(let_constraint);
        }
        if let Some(ret) = top_return_constraint(top) {
            return Some(Constraint::from_term(ret));
        }
    }
    None
}

fn let_assignment_constraint(
    source: &str,
    tokens: &[TokenSpan],
    assign_start: usize,
) -> Option<Constraint> {
    let let_idx = tokens
        .iter()
        .enumerate()
        .rev()
        .find(|(_, token)| token.span.start < assign_start && token.token == Token::KwLet)
        .map(|(idx, _)| idx)?;
    let colon = tokens[let_idx..]
        .iter()
        .find(|token| token.span.start < assign_start && token.token == Token::Colon)?;
    constraint_from_source(source, colon.span.end..assign_start)
}

fn top_return_constraint<'bump>(top: &TopLevel<'bump>) -> Option<&'bump Term<'bump>> {
    match top {
        TopLevel::TLPublic(inner) => top_return_constraint(inner),
        TopLevel::TLDef(_, _, ret, _, _) => *ret,
        TopLevel::TLExternDef(_, _, ret, _) => Some(*ret),
        TopLevel::TLCheck(_, constraint, _) => Some(*constraint),
        _ => None,
    }
}

fn function_argument_expected(
    source: &str,
    offset: usize,
    tokens: &[TokenSpan],
    symbols: &[Symbol],
) -> Option<Constraint> {
    let prefix_range = identifier_prefix_range(source, offset);
    if let Some(expected) =
        function_argument_expected_from_text(source, prefix_range.start, symbols)
    {
        return Some(expected);
    }
    let active_tokens: Vec<_> = tokens
        .iter()
        .filter(|token| token.span.end <= prefix_range.start)
        .collect();
    let mut atoms_since_delim = Vec::new();
    for token in active_tokens.iter().rev() {
        if is_expr_delimiter(&token.token) {
            break;
        }
        if is_atom_token(&token.token) {
            atoms_since_delim.push(*token);
        }
    }
    atoms_since_delim.reverse();
    let head = atoms_since_delim.first()?;
    let Token::Ident(name) = &head.token else {
        return None;
    };
    let arg_index = atoms_since_delim.len().saturating_sub(1);
    symbols
        .iter()
        .find(|symbol| symbol.name == *name)
        .and_then(|symbol| symbol.signature.as_ref())
        .and_then(|signature| signature.params.get(arg_index).cloned())
}

fn function_argument_expected_from_text(
    source: &str,
    prefix_start: usize,
    symbols: &[Symbol],
) -> Option<Constraint> {
    let line_start = source[..prefix_start].rfind('\n').map_or(0, |idx| idx + 1);
    let line = &source[line_start..prefix_start];
    let expr_start = line
        .rfind([',', ';', '(', '{'])
        .map_or(0, |idx| idx + 1)
        .max(line.rfind(":=").map_or(0, |idx| idx + 2))
        .max(line.rfind("<-").map_or(0, |idx| idx + 2))
        .max(line.rfind(" then ").map_or(0, |idx| idx + 6))
        .max(line.rfind(" else ").map_or(0, |idx| idx + 6));
    let mut fragment = line[expr_start..].trim_start();
    fragment = fragment
        .strip_prefix("#eval")
        .unwrap_or(fragment)
        .trim_start();
    fragment = fragment
        .strip_prefix("#check")
        .unwrap_or(fragment)
        .trim_start();
    if fragment.is_empty() || fragment.ends_with('.') || fragment.contains("::") {
        return None;
    }
    let words: Vec<_> = fragment.split_whitespace().collect();
    let head = words.first()?;
    if !head
        .chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_alphabetic() || ch == '_')
    {
        return None;
    }
    let arg_index = words.len().saturating_sub(1);
    symbols
        .iter()
        .find(|symbol| symbol.name == *head)
        .and_then(|symbol| symbol.signature.as_ref())
        .and_then(|signature| signature.params.get(arg_index).cloned())
}

fn if_condition_expected(offset: usize, tokens: &[TokenSpan]) -> Option<Constraint> {
    let last_then = last_token_before(tokens, offset, |t| t.token == Token::KwThen);
    let last_if = last_token_before(tokens, offset, |t| t.token == Token::KwIf);
    match (last_if, last_then) {
        (Some(if_tok), Some(then_tok)) if then_tok.span.start > if_tok.span.start => None,
        (Some(_), _) => Some(Constraint::named("bool")),
        _ => None,
    }
}

fn last_token_before<'a>(
    tokens: &'a [TokenSpan],
    offset: usize,
    pred: impl Fn(&'a TokenSpan) -> bool,
) -> Option<&'a TokenSpan> {
    tokens
        .iter()
        .take_while(|token| token.span.start < offset)
        .filter(|token| pred(token))
        .last()
}

fn is_atom_token(token: &Token) -> bool {
    matches!(
        token,
        Token::Ident(_) | Token::IntLit(_) | Token::StrLit(_) | Token::True | Token::False
    )
}

fn is_expr_delimiter(token: &Token) -> bool {
    matches!(
        token,
        Token::ColonEq
            | Token::Eq
            | Token::KwIn
            | Token::KwThen
            | Token::KwElse
            | Token::Semi
            | Token::Comma
            | Token::LParen
            | Token::LBrace
            | Token::Bar
            | Token::HashCheck
            | Token::HashEval
            | Token::KwDef
            | Token::KwLet
            | Token::KwDo
            | Token::LeftArrow
    )
}

pub(crate) fn constraint_from_source(source: &str, range: Range<usize>) -> Option<Constraint> {
    let text = source.get(range)?.trim();
    (!text.is_empty()).then(|| Constraint::new(text))
}

fn normal_candidates(symbols: &[Symbol], context: &CompletionContext) -> Vec<Symbol> {
    symbols
        .iter()
        .filter(|symbol| symbol.name.starts_with(&context.prefix))
        .filter(|symbol| {
            if symbol.kind == SymbolKind::Keyword {
                return true;
            }
            context
                .expected
                .as_ref()
                .is_none_or(|expected| symbol.satisfies_expected(expected))
        })
        .cloned()
        .collect()
}

fn dot_candidates(symbols: &[Symbol], context: &CompletionContext) -> Vec<Symbol> {
    let Some(receiver) = &context.receiver_constraint else {
        return Vec::new();
    };
    symbols
        .iter()
        .filter(|symbol| {
            symbol.name.starts_with(&context.prefix)
                || method_name(&symbol.name).starts_with(&context.prefix)
        })
        .filter(|symbol| interface_method_available(symbol, symbols, receiver))
        .cloned()
        .collect()
}

fn interface_method_available(symbol: &Symbol, symbols: &[Symbol], receiver: &Constraint) -> bool {
    if symbol.kind != SymbolKind::Function || !symbol.name.contains('.') {
        return false;
    }
    let Some(interface_name) = symbol.name.rsplit_once('.').map(|(head, _)| head) else {
        return false;
    };
    let first_param_matches = symbol
        .signature
        .as_ref()
        .and_then(|sig| sig.params.first())
        .is_some_and(|first| first.matches_expected(receiver));
    let method_param_matches = symbol.signature.as_ref().is_some_and(|sig| {
        let result = sig.result.display.trim();
        result.starts_with(&format!("({} ->", receiver.display))
            || result.starts_with(&format!("{} ->", receiver.display))
    });
    symbols.iter().any(|candidate| {
        if candidate.kind != SymbolKind::Value {
            return false;
        }
        let Some(constraint) = &candidate.constraint else {
            return false;
        };
        let parts = constraint.display.split_whitespace().collect::<Vec<_>>();
        if parts.first().copied() != Some(interface_name) {
            return false;
        }
        first_param_matches
            || method_param_matches
            || parts
                .get(1)
                .is_some_and(|arg| Constraint::named(arg).matches_expected(receiver))
    })
}

fn module_path_candidates(
    module_paths: &[Vec<String>],
    context: &CompletionContext,
) -> Vec<Symbol> {
    let prefix_path = &context.module_path_prefix;
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for path in module_paths {
        if path.len() <= prefix_path.len() {
            continue;
        }
        if !path[..prefix_path.len()].eq(prefix_path) {
            continue;
        }
        let segment = path[prefix_path.len()].clone();
        if !segment.starts_with(&context.prefix) || !seen.insert(segment.clone()) {
            continue;
        }
        out.push(Symbol {
            name: segment,
            detail: path[..=prefix_path.len()].join("::"),
            constraint: None,
            signature: None,
            kind: SymbolKind::Module,
            imported_path: Some(path[..=prefix_path.len()].to_vec()),
        });
    }
    out
}

fn qualified_path_candidates(symbols: &[Symbol], context: &CompletionContext) -> Vec<Symbol> {
    let prefix_path = context.module_path_prefix.join("::");
    let qualified_prefix = format!("{prefix_path}::");
    symbols
        .iter()
        .filter(|symbol| symbol.name.starts_with(&qualified_prefix))
        .filter(|symbol| {
            symbol
                .name
                .strip_prefix(&qualified_prefix)
                .is_some_and(|tail| !tail.contains("::") && tail.starts_with(&context.prefix))
        })
        .cloned()
        .collect()
}

fn collect_module_paths(symbols: &[Symbol]) -> Vec<Vec<String>> {
    let mut paths = Vec::new();
    for symbol in symbols {
        if let Some(path) = &symbol.imported_path {
            for i in 1..=path.len() {
                paths.push(path[..i].to_vec());
            }
        }
        if symbol.name.contains("::") {
            let path: Vec<_> = symbol.name.split("::").map(|s| s.to_string()).collect();
            for i in 1..=path.len() {
                paths.push(path[..i].to_vec());
            }
        }
    }
    paths.sort();
    paths.dedup();
    paths
}

fn sort_and_dedup(candidates: &mut Vec<Symbol>, context: &CompletionContext) {
    candidates.sort_by(|a, b| compare_symbols(a, b, context));
    let mut seen = HashSet::new();
    candidates.retain(|symbol| seen.insert(symbol.name.clone()));
}

fn compare_symbols(a: &Symbol, b: &Symbol, context: &CompletionContext) -> Ordering {
    let a_exact = a.name == context.prefix || method_name(&a.name) == context.prefix;
    let b_exact = b.name == context.prefix || method_name(&b.name) == context.prefix;
    b_exact
        .cmp(&a_exact)
        .then_with(|| constraint_rank(a, context).cmp(&constraint_rank(b, context)))
        .then_with(|| a.kind.base_rank().cmp(&b.kind.base_rank()))
        .then_with(|| display_name(a, context).cmp(&display_name(b, context)))
}

fn constraint_rank(symbol: &Symbol, context: &CompletionContext) -> u8 {
    match &context.expected {
        Some(expected) if symbol.satisfies_expected(expected) => 0,
        Some(_) => 2,
        None => 1,
    }
}

fn symbol_to_completion(symbol: Symbol, context: &CompletionContext) -> lsp::CompletionItem {
    let label = display_name(&symbol, context);
    let sort_rank = constraint_rank(&symbol, context);
    let kind_rank = symbol.kind.base_rank();
    let sort_name = symbol.name.clone();
    lsp::CompletionItem {
        label,
        kind: Some(symbol.kind.lsp_kind()),
        detail: Some(symbol.detail),
        sort_text: Some(format!("{sort_rank:02}_{kind_rank:02}_{sort_name}")),
        ..Default::default()
    }
}

fn display_name(symbol: &Symbol, context: &CompletionContext) -> String {
    if context.mode == CompletionMode::Dot {
        method_name(&symbol.name).to_string()
    } else if context.mode == CompletionMode::QualifiedPath {
        symbol
            .name
            .rsplit("::")
            .next()
            .unwrap_or(&symbol.name)
            .to_string()
    } else {
        symbol.name.clone()
    }
}

fn method_name(name: &str) -> &str {
    name.rsplit(['.', ':']).next().unwrap_or(name)
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

    fn satisfies_expected(&self, expected: &Constraint) -> bool {
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

pub(crate) fn top_level_ranges<'bump>(
    source: &str,
    ast: &crate::Ast<'bump>,
) -> Vec<(usize, usize, TopLevel<'bump>)> {
    top_level_ranges_from_tops(source, ast.top_levels().cloned())
}

pub(crate) fn top_level_ranges_from_tops<'bump>(
    source: &str,
    tops: impl IntoIterator<Item = TopLevel<'bump>>,
) -> Vec<(usize, usize, TopLevel<'bump>)> {
    let mut tops: Vec<_> = tops.into_iter().map(|top| (top_start(&top), top)).collect();
    tops.sort_by_key(|(start, _)| *start);
    let mut ranges = Vec::new();
    for idx in 0..tops.len() {
        let start = tops[idx].0;
        let end = tops
            .get(idx + 1)
            .map(|(next, _)| *next)
            .unwrap_or(source.len());
        ranges.push((start, end, tops[idx].1.clone()));
    }
    ranges
}

pub(crate) fn expanded_top_level_ranges<'bump>(
    source: &str,
    ast: &crate::Ast<'bump>,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Vec<(usize, usize, TopLevel<'bump>)> {
    let raw_ranges = top_level_ranges(source, ast);
    let mut tops = raw_ranges
        .iter()
        .map(|(_, _, top)| top.clone())
        .collect::<Vec<_>>();
    let mut compiler = Compiler::new(bump, arena);
    let work = raw_ranges
        .iter()
        .enumerate()
        .map(|(idx, (_, _, top))| (idx, top.clone(), false));
    let (expanded, _) = compiler.check_top_levels_with_expansion_for_diagnostics(
        work,
        "<lsp>",
        source,
        CheckMode::Fast,
    );
    for (idx, top) in expanded {
        if let Some(slot) = tops.get_mut(idx) {
            *slot = top;
        }
    }
    top_level_ranges_from_tops(source, tops)
}

pub(crate) fn top_start(top: &TopLevel<'_>) -> usize {
    match top {
        TopLevel::TLDef(_, _, _, _, span)
        | TopLevel::TLExternDef(_, _, _, span)
        | TopLevel::TLInstance(_, _, _, span)
        | TopLevel::TLVariable(_, span)
        | TopLevel::TLTheorem(_, _, _, span)
        | TopLevel::TLUse(_, _, span)
        | TopLevel::TLMod(_, span)
        | TopLevel::TLNamespace(_, _, span)
        | TopLevel::TLCheck(_, _, span)
        | TopLevel::TLEval(_, span)
        | TopLevel::TLExpr(_, span)
        | TopLevel::TLSplice(_, span) => span.start,
        TopLevel::TLPublic(inner) => top_start(inner),
        TopLevel::TLAttributed(_, inner, _) => top_start(inner),
    }
}
