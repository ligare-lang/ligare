use std::fmt;
use std::ops::Range;

use bumpalo::Bump;
use chumsky::Stream;
use chumsky::prelude::*;
use ligare::core::pool::TermArena;
use ligare::diagnostic::Span;
use ligare::front::lexer::Token;
use ligare::front::parser::{self, TopLevel};
use logos::Logos;

use crate::{Ast, AstNode, ErrorNode, ParseError};

type SpannedToken = (Token, Range<usize>);
type SpannedKind = (TokKind, Range<usize>);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HeaderKind {
    Def,
    ExternDef,
    Theorem,
    Use,
    Mod,
    Check,
    Eval,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TokKind {
    Newline,
    KwLet,
    KwIn,
    KwIf,
    KwThen,
    KwElse,
    True,
    False,
    KwBy,
    KwFun,
    KwFunc,
    KwDo,
    KwWhere,
    KwDef,
    KwExtern,
    KwUnsafe,
    KwPure,
    KwAuto,
    KwExact,
    KwApply,
    KwIntro,
    KwHave,
    KwTheorem,
    KwPub,
    KwUse,
    KwMod,
    KwNamespace,
    KwAs,
    KwStruct,
    KwEnum,
    KwMatch,
    KwWith,
    KwOf,
    Bar,
    HashGlobalAllocator,
    HashCheck,
    HashEval,
    BlockComment,
    ColonEq,
    PathSep,
    FatArrow,
    ThinArrow,
    Le,
    LeftArrow,
    Ge,
    Neq,
    EqEq,
    LParen,
    RParen,
    Semi,
    Comma,
    LBrace,
    RBrace,
    Colon,
    Dot,
    Backslash,
    Lambda,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Lt,
    Gt,
    Eq,
    And,
    Or,
    Not,
    Implies,
    AndIntro,
    AndElimLeft,
    IntLit,
    StrLit,
    Ident,
}

impl fmt::Display for TokKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

pub fn parse_program_lsp<'bump>(
    source: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> (Ast<'bump>, Vec<ParseError>) {
    let (tokens, mut errors) = tokenize(source);
    let chunks = split_top_level_chunks(source, &tokens);
    let mut items = Vec::new();

    for chunk in chunks {
        let chunk_tokens = &tokens[chunk.token_range.clone()];
        if starts_with_header(chunk_tokens) {
            let header_errors = validate_header(chunk_tokens, chunk.span.clone());
            errors.extend(header_errors);
        }

        match parser::parse_program(&source[chunk.span.clone()], bump, arena) {
            Ok(tops) => {
                for top in tops {
                    items.push(AstNode::TopLevel(offset_top_level(
                        top,
                        chunk.span.start,
                        arena,
                    )));
                }
            }
            Err(err) => {
                let span = offset_span(err.span, chunk.span.start);
                let message = err.message;
                errors.push(ParseError {
                    span: span.clone(),
                    message: message.clone(),
                });
                items.push(AstNode::Error(ErrorNode {
                    span: chunk.span.clone(),
                    message,
                }));
            }
        }
    }

    (Ast { items }, errors)
}

fn kind(token: &Token) -> TokKind {
    match token {
        Token::Newline => TokKind::Newline,
        Token::KwLet => TokKind::KwLet,
        Token::KwIn => TokKind::KwIn,
        Token::KwIf => TokKind::KwIf,
        Token::KwThen => TokKind::KwThen,
        Token::KwElse => TokKind::KwElse,
        Token::True => TokKind::True,
        Token::False => TokKind::False,
        Token::KwBy => TokKind::KwBy,
        Token::KwFun => TokKind::KwFun,
        Token::KwFunc => TokKind::KwFunc,
        Token::KwDo => TokKind::KwDo,
        Token::KwWhere => TokKind::KwWhere,
        Token::KwDef => TokKind::KwDef,
        Token::KwExtern => TokKind::KwExtern,
        Token::KwInstance => TokKind::KwDef,
        Token::KwUnsafe => TokKind::KwUnsafe,
        Token::KwPure => TokKind::KwPure,
        Token::KwAuto => TokKind::KwAuto,
        Token::KwExact => TokKind::KwExact,
        Token::KwApply => TokKind::KwApply,
        Token::KwIntro => TokKind::KwIntro,
        Token::KwHave => TokKind::KwHave,
        Token::KwTheorem => TokKind::KwTheorem,
        Token::KwPub => TokKind::KwPub,
        Token::KwUse => TokKind::KwUse,
        Token::KwMod => TokKind::KwMod,
        Token::KwNamespace => TokKind::KwNamespace,
        Token::KwAs => TokKind::KwAs,
        Token::KwStruct => TokKind::KwStruct,
        Token::KwEnum => TokKind::KwEnum,
        Token::KwMatch => TokKind::KwMatch,
        Token::KwWith => TokKind::KwWith,
        Token::KwOf => TokKind::KwOf,
        Token::Bar => TokKind::Bar,
        Token::HashGlobalAllocator => TokKind::HashGlobalAllocator,
        Token::HashCheck => TokKind::HashCheck,
        Token::HashEval => TokKind::HashEval,
        Token::BlockComment => TokKind::BlockComment,
        Token::ColonEq => TokKind::ColonEq,
        Token::PathSep => TokKind::PathSep,
        Token::FatArrow => TokKind::FatArrow,
        Token::ThinArrow => TokKind::ThinArrow,
        Token::Le => TokKind::Le,
        Token::LeftArrow => TokKind::LeftArrow,
        Token::Ge => TokKind::Ge,
        Token::Neq => TokKind::Neq,
        Token::EqEq => TokKind::EqEq,
        Token::LParen => TokKind::LParen,
        Token::RParen => TokKind::RParen,
        Token::Semi => TokKind::Semi,
        Token::Comma => TokKind::Comma,
        Token::LBrace => TokKind::LBrace,
        Token::RBrace => TokKind::RBrace,
        Token::Colon => TokKind::Colon,
        Token::Dot => TokKind::Dot,
        Token::Backslash => TokKind::Backslash,
        Token::Lambda => TokKind::Lambda,
        Token::Plus => TokKind::Plus,
        Token::Minus => TokKind::Minus,
        Token::Star => TokKind::Star,
        Token::Slash => TokKind::Slash,
        Token::Percent => TokKind::Percent,
        Token::Lt => TokKind::Lt,
        Token::Gt => TokKind::Gt,
        Token::Eq => TokKind::Eq,
        Token::And => TokKind::And,
        Token::Or => TokKind::Or,
        Token::Not => TokKind::Not,
        Token::Implies => TokKind::Implies,
        Token::AndIntro => TokKind::AndIntro,
        Token::AndElimLeft => TokKind::AndElimLeft,
        Token::IntLit(_) => TokKind::IntLit,
        Token::StrLit(_) => TokKind::StrLit,
        Token::Ident(_) => TokKind::Ident,
    }
}

fn tokenize(source: &str) -> (Vec<SpannedToken>, Vec<ParseError>) {
    let mut tokens = Vec::new();
    let mut errors = Vec::new();
    for (result, span) in Token::lexer(source).spanned() {
        match result {
            Ok(Token::BlockComment) => {}
            Ok(token) => tokens.push((token, span)),
            Err(()) => errors.push(ParseError {
                span: span.clone(),
                message: format!("invalid token `{}`", &source[span]),
            }),
        }
    }
    (tokens, errors)
}

#[derive(Debug, Clone)]
struct Chunk {
    token_range: Range<usize>,
    span: Range<usize>,
}

fn split_top_level_chunks(source: &str, tokens: &[SpannedToken]) -> Vec<Chunk> {
    let mut chunks = Vec::new();
    let mut start = first_non_newline(tokens, 0);

    while start < tokens.len() {
        let namespace_chunk = is_namespace_chunk_start(tokens, start);
        let mut end = start + 1;
        while end < tokens.len() {
            if is_sync_start(source, tokens, end)
                && (!namespace_chunk || is_top_level_boundary(tokens, start, end))
            {
                break;
            }
            end += 1;
        }

        let span_start = tokens[start].1.start;
        let span_end = tokens[end - 1].1.end;
        chunks.push(Chunk {
            token_range: start..end,
            span: span_start..span_end,
        });

        start = first_non_newline(tokens, end);
    }

    chunks
}

fn first_non_newline(tokens: &[SpannedToken], mut index: usize) -> usize {
    while matches!(tokens.get(index), Some((Token::Newline, _))) {
        index += 1;
    }
    index
}

fn is_namespace_chunk_start(tokens: &[SpannedToken], start: usize) -> bool {
    matches!(tokens.get(start), Some((Token::KwNamespace, _)))
        || matches!(tokens.get(start), Some((Token::KwPub, _)))
            && next_non_newline_kind(tokens, start + 1) == Some(TokKind::KwNamespace)
}

fn is_sync_start(source: &str, tokens: &[SpannedToken], index: usize) -> bool {
    if !is_line_start(source, tokens[index].1.start) {
        return false;
    }
    if matches!(
        previous_non_newline_kind(tokens, index),
        Some(TokKind::HashGlobalAllocator | TokKind::KwPub)
    ) {
        return false;
    }
    match tokens[index].0 {
        Token::KwDef
        | Token::KwExtern
        | Token::KwTheorem
        | Token::KwUse
        | Token::KwMod
        | Token::KwNamespace
        | Token::HashGlobalAllocator
        | Token::HashCheck
        | Token::HashEval => true,
        Token::KwPub => next_non_newline_kind(tokens, index + 1).is_some_and(|k| {
            matches!(
                k,
                TokKind::KwDef
                    | TokKind::KwExtern
                    | TokKind::KwTheorem
                    | TokKind::KwUse
                    | TokKind::KwMod
                    | TokKind::KwNamespace
            )
        }),
        _ => false,
    }
}

fn is_top_level_boundary(tokens: &[SpannedToken], start: usize, end: usize) -> bool {
    let mut parens = 0usize;
    let mut braces = 0usize;
    for (token, _) in &tokens[start..end] {
        match token {
            Token::LParen => parens += 1,
            Token::RParen => parens = parens.saturating_sub(1),
            Token::LBrace => braces += 1,
            Token::RBrace => braces = braces.saturating_sub(1),
            _ => {}
        }
    }
    parens == 0 && braces == 0
}

fn is_line_start(source: &str, offset: usize) -> bool {
    source[..offset]
        .rsplit_once('\n')
        .map_or(offset == 0, |(_, line)| line.trim().is_empty())
}

fn next_non_newline_kind(tokens: &[SpannedToken], mut index: usize) -> Option<TokKind> {
    while matches!(tokens.get(index), Some((Token::Newline, _))) {
        index += 1;
    }
    tokens.get(index).map(|(token, _)| kind(token))
}

fn previous_non_newline_kind(tokens: &[SpannedToken], index: usize) -> Option<TokKind> {
    let mut index = index;
    while index > 0 {
        index -= 1;
        if !matches!(tokens[index].0, Token::Newline) {
            return Some(kind(&tokens[index].0));
        }
    }
    None
}

fn validate_header(tokens: &[SpannedToken], eof_span: Span) -> Vec<ParseError> {
    if tokens.is_empty() {
        return Vec::new();
    }
    let kinds: Vec<SpannedKind> = tokens
        .iter()
        .map(|(token, span)| (kind(token), span.clone()))
        .collect();
    let stream = Stream::from_iter(eof_span, kinds.into_iter());
    let (_, errors) = header_parser().parse_recovery(stream);

    errors
        .into_iter()
        .map(|error| ParseError {
            span: error.span(),
            message: format!("{error}"),
        })
        .collect()
}

fn starts_with_header(tokens: &[SpannedToken]) -> bool {
    match tokens.first().map(|(token, _)| token) {
        Some(Token::KwPub) => true,
        Some(
            Token::KwDef
            | Token::KwExtern
            | Token::KwTheorem
            | Token::KwUse
            | Token::KwMod
            | Token::HashGlobalAllocator
            | Token::HashCheck
            | Token::HashEval,
        ) => true,
        _ => false,
    }
}

fn header_parser() -> impl Parser<TokKind, HeaderKind, Error = Simple<TokKind>> {
    let newlines = || just(TokKind::Newline).repeated().ignored();
    let def = just(TokKind::KwDef)
        .ignore_then(just(TokKind::Ident))
        .to(HeaderKind::Def);
    let extern_def = just(TokKind::KwExtern)
        .ignore_then(just(TokKind::KwDef))
        .ignore_then(just(TokKind::Ident))
        .to(HeaderKind::ExternDef);
    let theorem = just(TokKind::KwTheorem)
        .ignore_then(just(TokKind::Ident))
        .to(HeaderKind::Theorem);
    let use_ = just(TokKind::KwUse).to(HeaderKind::Use);
    let mod_ = just(TokKind::KwMod)
        .ignore_then(just(TokKind::Ident))
        .to(HeaderKind::Mod);
    let check = just(TokKind::HashCheck).to(HeaderKind::Check);
    let eval = just(TokKind::HashEval).to(HeaderKind::Eval);

    just(TokKind::HashGlobalAllocator)
        .then_ignore(newlines())
        .or_not()
        .ignore_then(just(TokKind::KwPub).then_ignore(newlines()).or_not())
        .ignore_then(choice((extern_def, def, theorem, use_, mod_, check, eval)))
        .recover_with(skip_then_retry_until([TokKind::Newline]))
}

fn offset_span(span: Span, offset: usize) -> Span {
    span.start + offset..span.end + offset
}

fn offset_top_level<'bump>(
    top: TopLevel<'bump>,
    offset: usize,
    arena: &'bump TermArena<'bump>,
) -> TopLevel<'bump> {
    match top {
        TopLevel::TLDef(name, params, ret, body, span) => {
            TopLevel::TLDef(name, params, ret, body, offset_span(span, offset))
        }
        TopLevel::TLExternDef(name, params, ret, span) => {
            TopLevel::TLExternDef(name, params, ret, offset_span(span, offset))
        }
        TopLevel::TLInstance(name, constraint, value, span) => {
            TopLevel::TLInstance(name, constraint, value, offset_span(span, offset))
        }
        TopLevel::TLTheorem(name, prop, body, span) => {
            TopLevel::TLTheorem(name, prop, body, offset_span(span, offset))
        }
        TopLevel::TLUse(imports, visibility, span) => {
            TopLevel::TLUse(imports, visibility, offset_span(span, offset))
        }
        TopLevel::TLMod(name, span) => TopLevel::TLMod(name, offset_span(span, offset)),
        TopLevel::TLNamespace(name, items, span) => {
            let shifted = items
                .iter()
                .cloned()
                .map(|item| offset_top_level(item, offset, arena))
                .collect::<Vec<_>>();
            TopLevel::TLNamespace(
                name,
                arena.bump().alloc_slice_clone(&shifted),
                offset_span(span, offset),
            )
        }
        TopLevel::TLPublic(inner) => {
            let shifted = offset_top_level((*inner).clone(), offset, arena);
            TopLevel::TLPublic(arena.bump().alloc(shifted))
        }
        TopLevel::TLCheck(term, constraint, span) => {
            TopLevel::TLCheck(term, constraint, offset_span(span, offset))
        }
        TopLevel::TLEval(term, span) => TopLevel::TLEval(term, offset_span(span, offset)),
        TopLevel::TLExpr(term, span) => TopLevel::TLExpr(term, offset_span(span, offset)),
    }
}
