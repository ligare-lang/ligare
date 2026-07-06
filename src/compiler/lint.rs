use crate::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use crate::config::{
    BUILTIN_PROP, COMPILER_BUILTIN_ATTRIBUTE_ATTR, COMPILER_INTRINSIC_ATTR, canonical_builtin_name,
};
use crate::core::syntax::Term;
use crate::diagnostic::{Diagnostic, Span};
use crate::front::parser::TopLevel;

pub(crate) fn naming_diagnostics<'bump>(tops: &[TopLevel<'bump>], source: &str) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    lint_siblings(tops, source, source.len(), &mut diagnostics);
    diagnostics
}

pub(crate) fn naming_indexed_diagnostics<'bump>(
    tops: &[(usize, TopLevel<'bump>, bool)],
    source: &str,
) -> Vec<(usize, Diagnostic)> {
    let mut items = tops
        .iter()
        .filter(|(idx, _, _)| *idx != usize::MAX)
        .map(|(idx, top, report)| IndexedTop {
            idx: *idx,
            report: *report,
            top,
        })
        .collect::<Vec<_>>();
    items.sort_by_key(|item| top_start(item.top));

    let mut diagnostics = Vec::new();
    lint_indexed_siblings(&items, source, source.len(), &mut diagnostics);
    diagnostics
}

#[derive(Clone, Copy)]
struct IndexedTop<'a, 'bump> {
    idx: usize,
    report: bool,
    top: &'a TopLevel<'bump>,
}

#[derive(Clone, Copy)]
enum ExpectedNaming {
    PascalCase { label: &'static str },
    SnakeCase { label: &'static str },
}

impl ExpectedNaming {
    fn label(self) -> &'static str {
        match self {
            Self::PascalCase { label } | Self::SnakeCase { label } => label,
        }
    }

    fn style_name(self) -> &'static str {
        match self {
            Self::PascalCase { .. } => "PascalCase",
            Self::SnakeCase { .. } => "snake_case",
        }
    }

    fn matches(self, name: &str) -> bool {
        match self {
            Self::PascalCase { .. } => is_pascal_case(name),
            Self::SnakeCase { .. } => is_snake_case(name),
        }
    }
}

fn lint_siblings<'bump>(
    tops: &[TopLevel<'bump>],
    source: &str,
    parent_end: usize,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for (idx, top) in tops.iter().enumerate() {
        let end = tops
            .get(idx + 1)
            .map(top_start)
            .unwrap_or(parent_end)
            .min(source.len());
        lint_top(top, source, end, diagnostics);
    }
}

fn lint_indexed_siblings<'a, 'bump>(
    tops: &[IndexedTop<'a, 'bump>],
    source: &str,
    parent_end: usize,
    diagnostics: &mut Vec<(usize, Diagnostic)>,
) {
    for (idx, item) in tops.iter().enumerate() {
        if !item.report {
            continue;
        }
        let end = tops
            .get(idx + 1)
            .map(|next| top_start(next.top))
            .unwrap_or(parent_end)
            .min(source.len());
        let mut item_diagnostics = Vec::new();
        lint_top(item.top, source, end, &mut item_diagnostics);
        diagnostics.extend(
            item_diagnostics
                .into_iter()
                .map(|diagnostic| (item.idx, diagnostic)),
        );
    }
}

fn lint_top(
    top: &TopLevel<'_>,
    source: &str,
    search_end: usize,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if top.has_attribute(COMPILER_INTRINSIC_ATTR)
        || top.has_attribute(COMPILER_BUILTIN_ATTRIBUTE_ATTR)
    {
        return;
    }

    match top {
        TopLevel::TLDef(name, _, ret, body, _) => {
            let expected = if is_constraint_like_def(*ret, body) {
                ExpectedNaming::PascalCase {
                    label: "constraint/type",
                }
            } else {
                ExpectedNaming::SnakeCase {
                    label: "definition",
                }
            };
            push_naming_warning(top, name, expected, source, search_end, diagnostics);
        }
        TopLevel::TLExternDef(name, ..) => {
            push_naming_warning(
                top,
                name,
                ExpectedNaming::SnakeCase {
                    label: "extern definition",
                },
                source,
                search_end,
                diagnostics,
            );
        }
        TopLevel::TLInstance(name, ..) => {
            push_naming_warning(
                top,
                name,
                ExpectedNaming::SnakeCase { label: "instance" },
                source,
                search_end,
                diagnostics,
            );
        }
        TopLevel::TLTheorem(name, ..) => {
            push_naming_warning(
                top,
                name,
                ExpectedNaming::SnakeCase { label: "theorem" },
                source,
                search_end,
                diagnostics,
            );
        }
        TopLevel::TLNamespace(_, items, _) => {
            lint_siblings(items, source, search_end, diagnostics);
        }
        TopLevel::TLPublic(inner) | TopLevel::TLAttributed(_, inner, _) => {
            lint_top(inner, source, search_end, diagnostics);
        }
        TopLevel::TLVariable(..)
        | TopLevel::TLUse(..)
        | TopLevel::TLMod(..)
        | TopLevel::TLCheck(..)
        | TopLevel::TLEval(..)
        | TopLevel::TLExpr(..)
        | TopLevel::TLSplice(..) => {}
    }
}

fn push_naming_warning(
    top: &TopLevel<'_>,
    name: &str,
    expected: ExpectedNaming,
    source: &str,
    search_end: usize,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if expected.matches(name) {
        return;
    }
    let span = name_span(top, source, search_end, name);
    diagnostics.push(Diagnostic::warning_with_span(
        format!(
            "README naming convention: {} `{name}` should use {}",
            expected.label(),
            expected.style_name()
        ),
        span,
    ));
}

fn name_span(top: &TopLevel<'_>, source: &str, search_end: usize, name: &str) -> Span {
    let start = top_start(top).min(source.len());
    let end = search_end.max(start).min(source.len());
    find_name_in_span(source, start..end, name).unwrap_or(start..start)
}

fn find_name_in_span(source: &str, span: Span, name: &str) -> Option<Span> {
    let start = span.start.min(source.len());
    let end = span.end.min(source.len()).max(start);
    source[start..end]
        .find(name)
        .map(|offset| start + offset..start + offset + name.len())
        .or_else(|| source.find(name).map(|offset| offset..offset + name.len()))
}

fn top_start(top: &TopLevel<'_>) -> usize {
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
        TopLevel::TLPublic(inner) | TopLevel::TLAttributed(_, inner, _) => top_start(inner),
    }
}

fn is_constraint_like_def(ret: Option<&Term<'_>>, body: &Term<'_>) -> bool {
    ret.is_some_and(term_is_prop_universe_like) || term_is_type_definition_like(body)
}

fn term_is_prop_universe_like(term: &Term<'_>) -> bool {
    match strip_wrappers(term) {
        Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
            canonical_builtin_name(name) == BUILTIN_PROP
        }
        _ => false,
    }
}

fn term_is_type_definition_like(term: &Term<'_>) -> bool {
    match strip_wrappers(term) {
        Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
            looks_like_constraint_name(name)
        }
        Term::App(head, _) => term_is_type_definition_like(head),
        Term::Refine(..) | Term::StructDef(..) | Term::EnumDef(..) => true,
        _ => false,
    }
}

fn strip_wrappers<'a, 'bump>(mut term: &'a Term<'bump>) -> &'a Term<'bump> {
    loop {
        term = match term {
            Term::Annot(inner, _)
            | Term::Implicit(inner)
            | Term::Unsafe(inner)
            | Term::Pure(inner)
            | Term::Quote(inner)
            | Term::Splice(inner) => inner,
            _ => return term,
        };
    }
}

fn looks_like_constraint_name(name: &str) -> bool {
    let leaf = name.rsplit("::").next().unwrap_or(name);
    BUILTIN_CONSTRAINT_NAMES.contains(&canonical_builtin_name(leaf)) || is_pascal_case(leaf)
}

fn is_pascal_case(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(ch) if ch.is_ascii_uppercase())
        && !name.contains('_')
        && chars.all(|ch| ch.is_ascii_alphanumeric())
}

fn is_snake_case(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(ch) if ch.is_ascii_lowercase() || ch == '_')
        && chars.all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '_')
}

#[cfg(test)]
mod tests {
    use super::*;
    use bumpalo::Bump;

    use crate::core::pool::TermArena;
    use crate::front::parser::parse_program;

    fn parse(source: &str) -> Vec<TopLevel<'static>> {
        let bump = Box::leak(Box::new(Bump::new()));
        let arena = Box::leak(Box::new(TermArena::new(bump)));
        parse_program(source, bump, arena).expect("parse program")
    }

    #[test]
    fn naming_lint_distinguishes_types_and_values() {
        let source = "def bad_type : prop := enum\n  | One\ndef BadValue : int := 1\ntheorem BadTheorem : int := 0\n";
        let tops = parse(source);
        let diagnostics = naming_diagnostics(&tops, source);

        assert_eq!(diagnostics.len(), 3, "{diagnostics:#?}");
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.severity == crate::diagnostic::Severity::Warning)
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("constraint/type `bad_type`"))
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("definition `BadValue`"))
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("theorem `BadTheorem`"))
        );
    }

    #[test]
    fn naming_lint_skips_compiler_intrinsics() {
        let source = "#[compiler_intrinsic]\ndef int : prop := data\n";
        let tops = parse(source);
        let diagnostics = naming_diagnostics(&tops, source);

        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}
