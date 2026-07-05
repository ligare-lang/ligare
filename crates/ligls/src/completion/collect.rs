use ligare::checker::CheckMode;
use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::core::syntax::{Name, Term};
use ligare::front::lexer::Token;
use ligare::front::parser::TopLevel;
use ligare::pretty::PrettyPrinter;

use super::{
    Constraint, KEYWORDS, META_EXPR_TYPE, META_EXPR_VARIANTS, Signature, Symbol, SymbolKind,
    TokenSpan, constraint_from_source,
};

pub(super) fn collect_symbols<'bump>(
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
                    name: format!("{type_name}::{variant_name}"),
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

pub(super) fn keyword_symbols() -> Vec<Symbol> {
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

pub(super) fn builtin_symbols() -> Vec<Symbol> {
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

fn meta_symbols() -> Vec<Symbol> {
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

pub(super) fn collect_module_paths(symbols: &[Symbol]) -> Vec<Vec<String>> {
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

pub(crate) fn top_level_ranges<'bump>(
    source: &str,
    ast: &crate::Ast<'bump>,
) -> Vec<(usize, usize, TopLevel<'bump>)> {
    top_level_ranges_from_tops(source, ast.top_levels().cloned())
}

fn top_level_ranges_from_tops<'bump>(
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
    bump: &'bump bumpalo::Bump,
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
