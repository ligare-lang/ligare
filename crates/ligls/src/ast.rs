use std::fmt;

use ligare::diagnostic::Span;
use ligare::front::parser::TopLevel;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub span: Span,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at {}..{}",
            self.message, self.span.start, self.span.end
        )
    }
}

impl std::error::Error for ParseError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrorNode {
    pub span: Span,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AstNode<'bump> {
    TopLevel(TopLevel<'bump>),
    Error(ErrorNode),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ast<'bump> {
    pub items: Vec<AstNode<'bump>>,
}

impl<'bump> Ast<'bump> {
    pub fn top_levels(&self) -> impl Iterator<Item = &TopLevel<'bump>> {
        self.items.iter().filter_map(|node| match node {
            AstNode::TopLevel(top) => Some(top),
            AstNode::Error(_) => None,
        })
    }
}
