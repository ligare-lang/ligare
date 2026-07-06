use logos::Logos;

use bumpalo::Bump;

use super::{ParseError, ParsedDef, Parser, SpannedToken, TopLevel};
use crate::core::pool::{StringPool, TermArena};
use crate::core::syntax::Term;
use crate::front::lexer::Token;

fn tokenize(input: &str) -> Result<Vec<SpannedToken>, ParseError> {
    let mut tokens = Vec::new();
    for (result, span) in Token::lexer(input).spanned() {
        match result {
            Ok(Token::BlockComment) => {}
            Ok(token) => tokens.push((token, span)),
            Err(()) => {
                return Err(ParseError {
                    message: format!("invalid token `{}`", &input[span.clone()]),
                    span,
                });
            }
        }
    }
    Ok(tokens)
}

pub fn parse_expr_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<&'bump Term<'bump>, ParseError> {
    let pool = StringPool::new(bump);
    let tokens = tokenize(input)?;
    Parser::new(&tokens, &pool, arena).parse_expr_top()
}

pub fn parse_def_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<ParsedDef<'bump>, String> {
    let pool = StringPool::new(bump);
    let tokens = tokenize(input).map_err(|e| e.to_string())?;
    Parser::new(&tokens, &pool, arena)
        .parse_def_top()
        .map_err(|e| e.to_string())
}

pub fn parse_program<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<Vec<TopLevel<'bump>>, ParseError> {
    let pool = StringPool::new(bump);
    let tokens = tokenize(input)?;
    Parser::new(&tokens, &pool, arena).parse_program()
}
