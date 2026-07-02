use crate::core::pool::{StringPool, TermArena};
use crate::core::syntax::{Name, Term};
use crate::diagnostic::Span;
use crate::front::lexer::Token;

mod api;
mod cursor;
mod declarations;
mod expressions;
mod top;

#[cfg(test)]
mod tests;

pub use api::{parse_def_top, parse_expr_top, parse_program};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UseTree<'bump> {
    pub path: &'bump [Name<'bump>],
    pub alias: Option<Name<'bump>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Visibility {
    Private,
    Public,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopLevel<'bump> {
    /// name, params, ret-annotation, desugared-body (Annot(Lam(...), Pi(...))), span
    TLDef(
        Name<'bump>,
        &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        Option<&'bump Term<'bump>>,
        &'bump Term<'bump>,
        Span,
    ),
    /// External C function declaration: name, params, return constraint, span.
    TLExternDef(
        Name<'bump>,
        &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        &'bump Term<'bump>,
        Span,
    ),
    /// Compile-time implicit instance: name, constraint, value, span.
    TLInstance(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>, Span),
    TLTheorem(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>, Span),
    TLUse(&'bump [UseTree<'bump>], Visibility, Span),
    TLMod(Name<'bump>, Span),
    TLPublic(&'bump TopLevel<'bump>),
    TLCheck(&'bump Term<'bump>, &'bump Term<'bump>, Span),
    TLEval(&'bump Term<'bump>, Span),
    TLExpr(&'bump Term<'bump>, Span),
}

pub(super) const KEYWORDS: &[&str] = &[
    "let", "in", "if", "then", "else", "true", "false", "by", "fun", "func", "where", "def", "do",
    "extern", "instance", "unsafe", "pure", "auto", "theorem", "pub", "use", "mod", "as",
];

/// Names that represent language builtins (not user-defined).
pub(super) const BUILTIN_NAMES: &[&str] = &[
    "int", "bool", "str", "IO", "()", "data", "prop", "theorem", "proof", "and", "or", "not",
    "implies", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "c_int", "c_uint", "ptr",
    "ptr_cast",
];

pub(super) type SpannedToken = (Token, std::ops::Range<usize>);

/// Parsed top-level definition: (name, params, ret_annotation, body).
pub type ParsedDef<'bump> = (
    Name<'bump>,
    &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
    Option<&'bump Term<'bump>>,
    &'bump Term<'bump>,
);

/// Parsed function body: (params, ret_annotation, body).
pub(super) type ParsedFuncBody<'bump> = (
    Vec<(Name<'bump>, Option<&'bump Term<'bump>>)>,
    Option<&'bump Term<'bump>>,
    &'bump Term<'bump>,
);

/// Parsed named match branch (with Vec instead of slice during parsing).
pub(super) type ParsedMatchBranch<'bump> = (
    Name<'bump>,
    Vec<(Name<'bump>, &'bump Term<'bump>)>,
    &'bump Term<'bump>,
);

// The parser intentionally has one expression grammar for every term. Outer
// grammar productions own their delimiters and parse the delimited token slice
// with that same expression grammar.

pub struct Parser<'a, 'bump> {
    tokens: &'a [SpannedToken],
    pos: usize,
    pool: &'a StringPool<'bump>,
    arena: &'a TermArena<'bump>,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} at {}..{}",
            self.message, self.span.start, self.span.end
        )
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Associativity {
    Left,
    Right,
    None,
}
