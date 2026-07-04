use std::ops::Range;

use ligare::core::syntax::Term;
use ligare::front::lexer::Token;
use ligare::front::parser::TopLevel;

use super::{
    CompletionContext, CompletionMode, Constraint, Symbol, TokenSpan, constraint_from_source,
};

pub(super) fn build_context(
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
