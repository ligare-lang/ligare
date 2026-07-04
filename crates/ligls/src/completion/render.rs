use std::cmp::Ordering;
use std::collections::HashSet;

use tower_lsp::lsp_types as lsp;

use super::{CompletionContext, CompletionMode, Constraint, Symbol, SymbolKind};

pub(super) fn normal_candidates(symbols: &[Symbol], context: &CompletionContext) -> Vec<Symbol> {
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

pub(super) fn dot_candidates(symbols: &[Symbol], context: &CompletionContext) -> Vec<Symbol> {
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

pub(super) fn module_path_candidates(
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

pub(super) fn qualified_path_candidates(
    symbols: &[Symbol],
    context: &CompletionContext,
) -> Vec<Symbol> {
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

pub(super) fn sort_and_dedup(candidates: &mut Vec<Symbol>, context: &CompletionContext) {
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

pub(super) fn symbol_to_completion(
    symbol: Symbol,
    context: &CompletionContext,
) -> lsp::CompletionItem {
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
