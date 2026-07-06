use super::{ParseError, Parser, SpannedToken};
use crate::core::pool::{StringPool, TermArena};
use crate::front::lexer::Token;

impl<'a, 'bump> Parser<'a, 'bump> {
    pub fn new(
        tokens: &'a [SpannedToken],
        pool: &'a StringPool<'bump>,
        arena: &'a TermArena<'bump>,
    ) -> Self {
        Self {
            tokens,
            pos: 0,
            pool,
            arena,
        }
    }

    pub(super) fn peek(&self) -> Option<&SpannedToken> {
        let mut i = self.pos;
        loop {
            match self.tokens.get(i) {
                Some((Token::Newline, _)) => i += 1,
                other => return other,
            }
        }
    }

    pub(super) fn peek_token(&self) -> Option<Token> {
        self.peek().map(|(t, _)| t.clone())
    }

    pub(super) fn advance(&mut self) {
        while matches!(self.tokens.get(self.pos), Some((Token::Newline, _))) {
            self.pos += 1;
        }
        self.pos += 1;
        while matches!(self.tokens.get(self.pos), Some((Token::Newline, _))) {
            self.pos += 1;
        }
    }

    pub(super) fn expect(&mut self, expected: &Token) -> Result<(), ParseError> {
        match self.peek() {
            Some((t, span)) if t == expected => {
                self.advance();
                Ok(())
            }
            Some((t, span)) => Err(ParseError {
                message: format!("expected {:?}, found {:?}", expected, t),
                span: span.clone(),
            }),
            None => Err(ParseError {
                message: format!("expected {:?}, found EOF", expected),
                span: 0..0,
            }),
        }
    }

    pub(super) fn try_expect(&mut self, expected: &Token) -> bool {
        if self.peek_token().as_ref() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    pub(super) fn is_at_end(&self) -> bool {
        self.peek().is_none()
    }

    pub(super) fn current_span(&self) -> std::ops::Range<usize> {
        self.peek().map(|(_, s)| s.clone()).unwrap_or(0..0)
    }

    pub(super) fn peek_ahead_is(&self, tok: &Token) -> bool {
        self.tokens
            .get(self.pos + 1)
            .map(|(t, _)| t == tok)
            .unwrap_or(false)
    }

    pub(super) fn try_parse<T>(
        &mut self,
        tok: Token,
        parse_fn: impl FnOnce(&mut Self) -> Result<T, ParseError>,
    ) -> Option<T> {
        if self.peek_token() != Some(tok) {
            return None;
        }
        let saved = self.pos;
        self.advance();
        match parse_fn(self) {
            Ok(t) => Some(t),
            Err(_) => {
                self.pos = saved;
                None
            }
        }
    }
}
