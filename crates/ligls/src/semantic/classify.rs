use std::collections::HashSet;
use std::ops::Range;

use ligare::core::syntax::{Term, Universe};
use ligare::front::lexer::Token;
use ligare::front::parser::TopLevel;

use super::{SemanticKind, SemanticModel, TokenSpan};
use crate::completion::top_start;

pub(super) fn definition_kind(
    params: &[(ligare::core::syntax::Name<'_>, Option<&Term<'_>>)],
    ret: Option<&Term<'_>>,
    body: &Term<'_>,
) -> SemanticKind {
    if is_constraint_definition(body) || ret.is_some_and(is_constraint_definition) {
        SemanticKind::Constraint
    } else if !params.is_empty()
        || ret.is_some_and(is_function_constraint)
        || is_function_value(body)
    {
        SemanticKind::Function
    } else {
        SemanticKind::Variable
    }
}

pub(super) fn is_type_parameter_constraint(term: &Term<'_>) -> bool {
    match term {
        Term::Implicit(inner) => is_type_parameter_constraint(inner),
        Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
            matches!(*name, "prop" | "theorem" | "proof")
        }
        Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
        _ => false,
    }
}

fn is_function_value(term: &Term<'_>) -> bool {
    match term {
        Term::Annot(inner, constraint) => {
            is_function_value(inner) || is_function_constraint(constraint)
        }
        Term::Lam(_) | Term::NamedLam(..) | Term::Pi(..) => true,
        _ => false,
    }
}

fn is_function_constraint(term: &Term<'_>) -> bool {
    matches!(term, Term::Pi(..))
}

pub(super) fn collect_constraint_names(term: &Term<'_>, constraints: &mut HashSet<String>) {
    match term {
        Term::Named(name) | Term::Global(name) | Term::Builtin(name) => {
            constraints.insert((*name).to_string());
        }
        Term::Implicit(inner) => collect_constraint_names(inner, constraints),
        Term::App(f, a) | Term::Annot(f, a) | Term::Pi(_, f, a) | Term::Refine(_, f, a) => {
            collect_constraint_names(f, constraints);
            collect_constraint_names(a, constraints);
        }
        _ => {}
    }
}

fn is_constraint_definition(term: &Term<'_>) -> bool {
    match term {
        Term::Annot(inner, constraint) => {
            is_constraint_definition(inner) || matches!(constraint, Term::Universe(Universe::UProp))
        }
        Term::EnumDef(..)
        | Term::StructDef(..)
        | Term::Refine(..)
        | Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
        Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
            matches!(*name, "prop" | "theorem" | "proof")
        }
        _ => false,
    }
}

pub(super) fn collect_type_members(
    _type_name: &str,
    qualified_type_name: &str,
    term: &Term<'_>,
    model: &mut SemanticModel,
) {
    let inner = match term {
        Term::Annot(inner, _) => *inner,
        other => other,
    };
    let namespace = qualified_type_name
        .rsplit_once("::")
        .map(|(namespace, _)| namespace);
    match inner {
        Term::EnumDef(_, variants) => {
            for (variant, _) in *variants {
                model
                    .constructors
                    .insert(format!("{qualified_type_name}::{variant}"));
                model.constructors.insert((*variant).to_string());
            }
        }
        Term::StructDef(_, fields) => {
            model
                .constructors
                .insert(format!("{qualified_type_name}.mk"));
            if namespace.is_none() {
                model.constructors.insert("mk".to_string());
            }
            for (field, _) in *fields {
                model
                    .functions
                    .insert(format!("{qualified_type_name}.{field}"));
                if namespace.is_none() {
                    model.functions.insert((*field).to_string());
                }
            }
        }
        _ => {}
    }
}

pub(super) fn dotted_kind(
    tokens: &[TokenSpan],
    idx: usize,
    model: &SemanticModel,
) -> Option<SemanticKind> {
    let token = tokens.get(idx)?;
    let Token::Ident(name) = &token.token else {
        return None;
    };
    if tokens
        .get(idx + 1)
        .is_some_and(|token| token.token == Token::Dot)
    {
        return model.global_kind(name).or(Some(SemanticKind::Constraint));
    }
    if idx >= 2 && tokens[idx - 1].token == Token::Dot {
        let Token::Ident(parent) = &tokens[idx - 2].token else {
            return model.global_kind(name);
        };
        let parent_path =
            qualified_path_ending_at(tokens, idx - 2).unwrap_or_else(|| parent.clone());
        let dotted = format!("{parent_path}.{name}");
        if model.functions.contains(&dotted) {
            Some(SemanticKind::Function)
        } else {
            model.global_kind(name)
        }
    } else {
        None
    }
}

pub(super) fn qualified_path_kind(
    tokens: &[TokenSpan],
    idx: usize,
    model: &SemanticModel,
) -> Option<SemanticKind> {
    let path = qualified_path_at(tokens, idx)?;
    if path.parts.len() <= 1 {
        return None;
    }
    if path.part_index + 1 < path.parts.len() {
        if path.part_index + 1 == path.parts.len() - 1
            && model
                .global_kind(&path.parts.join("::"))
                .is_some_and(|kind| {
                    matches!(kind, SemanticKind::Constructor | SemanticKind::Function)
                })
        {
            let prefix = path.parts[..=path.part_index].join("::");
            return model
                .global_kind(&prefix)
                .or_else(|| model.global_kind(path.parts[path.part_index].as_str()))
                .or(Some(SemanticKind::Namespace));
        }
        return Some(SemanticKind::Namespace);
    }
    let name = path.parts[path.part_index].as_str();
    model
        .global_kind(&path.parts.join("::"))
        .or_else(|| model.global_kind(name))
}

struct QualifiedPath {
    parts: Vec<String>,
    part_index: usize,
}

fn qualified_path_at(tokens: &[TokenSpan], idx: usize) -> Option<QualifiedPath> {
    let Token::Ident(_) = tokens.get(idx)?.token else {
        return None;
    };

    let mut start = idx;
    while start >= 2
        && tokens[start - 1].token == Token::PathSep
        && matches!(tokens[start - 2].token, Token::Ident(_))
    {
        start -= 2;
    }

    let mut end = idx;
    while tokens
        .get(end + 1)
        .is_some_and(|token| token.token == Token::PathSep)
        && tokens
            .get(end + 2)
            .is_some_and(|token| matches!(token.token, Token::Ident(_)))
    {
        end += 2;
    }

    let mut parts = Vec::new();
    let mut part_index = None;
    let mut cursor = start;
    while cursor <= end {
        let Token::Ident(name) = &tokens[cursor].token else {
            return None;
        };
        if cursor == idx {
            part_index = Some(parts.len());
        }
        parts.push(name.clone());
        cursor += 2;
    }

    Some(QualifiedPath {
        parts,
        part_index: part_index?,
    })
}

fn qualified_path_ending_at(tokens: &[TokenSpan], idx: usize) -> Option<String> {
    let path = qualified_path_at(tokens, idx)?;
    (path.part_index + 1 == path.parts.len() && path.parts.len() > 1).then(|| path.parts.join("::"))
}

pub(super) fn is_attribute_path_token(tokens: &[TokenSpan], idx: usize) -> bool {
    if !matches!(
        tokens.get(idx).map(|token| &token.token),
        Some(Token::Ident(_))
    ) {
        return false;
    }

    let mut start = idx;
    while start >= 2
        && tokens[start - 1].token == Token::PathSep
        && matches!(tokens[start - 2].token, Token::Ident(_))
    {
        start -= 2;
    }

    start > 0 && tokens[start - 1].token == Token::HashLBracket
}

pub(super) fn qualified_name(namespace: Option<&str>, name: &str) -> String {
    namespace
        .map(|namespace| format!("{namespace}::{name}"))
        .unwrap_or_else(|| name.to_string())
}

pub(super) fn namespace_item_ranges<'a, 'bump>(
    items: &'a [TopLevel<'bump>],
    namespace_range: &Range<usize>,
) -> Vec<(Range<usize>, &'a TopLevel<'bump>)> {
    let mut starts: Vec<_> = items.iter().map(|item| (top_start(item), item)).collect();
    starts.sort_by_key(|(start, _)| *start);
    starts
        .iter()
        .enumerate()
        .map(|(idx, (start, item))| {
            let end = starts
                .get(idx + 1)
                .map(|(next, _)| *next)
                .unwrap_or(namespace_range.end);
            ((*start)..end, *item)
        })
        .collect()
}

pub(super) fn ident_after(tokens: &[TokenSpan], idx: usize) -> Option<(String, Range<usize>)> {
    tokens.get(idx + 1).and_then(|token| match &token.token {
        Token::Ident(name) => Some((name.clone(), token.span.clone())),
        _ => None,
    })
}

pub(super) fn is_do_bind_name(tokens: &[TokenSpan], idx: usize, range: &Range<usize>) -> bool {
    matches!(
        tokens.get(idx).map(|token| &token.token),
        Some(Token::Ident(_))
    ) && tokens
        .get(idx + 1)
        .is_some_and(|token| token.token == Token::LeftArrow)
        && tokens
            .get(idx)
            .is_some_and(|token| range.start <= token.span.start && token.span.end <= range.end)
}

pub(super) fn is_use_path_token(tokens: &[TokenSpan], idx: usize) -> bool {
    let Some(token) = tokens.get(idx) else {
        return false;
    };
    if !matches!(token.token, Token::Ident(_)) {
        return false;
    }
    let mut i = idx;
    while i > 0
        && matches!(
            tokens[i - 1].token,
            Token::PathSep | Token::Ident(_) | Token::Comma | Token::LBrace | Token::RBrace
        )
    {
        i -= 1;
    }
    i > 0 && tokens[i - 1].token == Token::KwUse
}

pub(super) fn is_keyword(token: &Token) -> bool {
    matches!(
        token,
        Token::KwLet
            | Token::KwIn
            | Token::KwIf
            | Token::KwThen
            | Token::KwElse
            | Token::True
            | Token::False
            | Token::KwBy
            | Token::KwFun
            | Token::KwFunc
            | Token::KwDo
            | Token::KwWhere
            | Token::KwDef
            | Token::KwExtern
            | Token::KwUnsafe
            | Token::KwPure
            | Token::KwAuto
            | Token::KwExact
            | Token::KwApply
            | Token::KwIntro
            | Token::KwHave
            | Token::KwTheorem
            | Token::KwPub
            | Token::KwUse
            | Token::KwMod
            | Token::KwNamespace
            | Token::KwAs
            | Token::KwStruct
            | Token::KwEnum
            | Token::KwMatch
            | Token::KwWith
            | Token::KwOf
            | Token::HashCheck
            | Token::HashEval
    )
}

pub(super) fn unwrap_public<'a, 'bump>(top: &'a TopLevel<'bump>) -> (bool, &'a TopLevel<'bump>) {
    let mut top = top;
    let mut public = false;
    loop {
        match top {
            TopLevel::TLPublic(inner) => {
                public = true;
                top = inner;
            }
            TopLevel::TLAttributed(_, inner, _) => top = inner,
            other => return (public, other),
        }
    }
}
