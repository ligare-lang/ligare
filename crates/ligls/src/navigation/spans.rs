use ligare::front::lexer::Token;

use super::{Constraint, IndexedDocument, TokenSpan};
use crate::completion::{constraint_from_source, infer_literal_constraint};

impl IndexedDocument {
    pub(super) fn tokens_between(
        &self,
        start: usize,
        end: usize,
    ) -> impl Iterator<Item = &TokenSpan> {
        self.tokens
            .iter()
            .filter(move |token| start <= token.span.start && token.span.end <= end)
    }

    pub(super) fn find_decl_name_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        let mut after_header = false;
        for token in self.tokens_between(start, end) {
            match &token.token {
                Token::KwDef | Token::KwTheorem | Token::KwMod => after_header = true,
                Token::Ident(candidate) if after_header && candidate == name => {
                    return Some(token.span.clone());
                }
                Token::Newline if !after_header => {}
                _ => {}
            }
        }
        None
    }

    pub(super) fn find_ident_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        self.tokens_between(start, end)
            .find_map(|token| match &token.token {
                Token::Ident(candidate) if candidate == name => Some(token.span.clone()),
                _ => None,
            })
    }

    pub(super) fn find_last_path_segment_span(
        &self,
        start: usize,
        end: usize,
        path: &[String],
    ) -> Option<std::ops::Range<usize>> {
        let name = path.last()?;
        self.tokens_between(start, end)
            .filter_map(|token| match &token.token {
                Token::Ident(candidate) if candidate == name => Some(token.span.clone()),
                _ => None,
            })
            .last()
    }

    pub(super) fn find_param_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        self.tokens_between(start, end)
            .collect::<Vec<_>>()
            .windows(2)
            .find_map(|window| {
                (window[0].token == Token::LParen)
                    .then_some(&window[1])
                    .and_then(|token| match &token.token {
                        Token::Ident(candidate) if candidate == name => Some(token.span.clone()),
                        _ => None,
                    })
            })
    }

    pub(super) fn find_enum_variant_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        self.tokens_between(start, end)
            .collect::<Vec<_>>()
            .windows(2)
            .find_map(|window| {
                (window[0].token == Token::Bar)
                    .then_some(&window[1])
                    .and_then(|token| match &token.token {
                        Token::Ident(candidate) if candidate == name => Some(token.span.clone()),
                        _ => None,
                    })
            })
    }

    pub(super) fn find_struct_field_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        let mut after_struct = false;
        let tokens: Vec<_> = self.tokens_between(start, end).collect();
        for window in tokens.windows(2) {
            if window[0].token == Token::KwStruct {
                after_struct = true;
                continue;
            }
            if after_struct
                && let Token::Ident(candidate) = &window[0].token
                && candidate == name
                && window[1].token == Token::Colon
            {
                return Some(window[0].span.clone());
            }
        }
        None
    }

    pub(super) fn let_constraint(&self, let_idx: usize, end: usize) -> Option<Constraint> {
        let mut j = let_idx + 2;
        if self
            .tokens
            .get(j)
            .is_some_and(|token| token.token == Token::Colon)
        {
            let constraint_start = self.tokens[j].span.end;
            j += 1;
            while self.tokens.get(j).is_some_and(|token| {
                token.span.start < end
                    && !matches!(
                        token.token,
                        Token::ColonEq | Token::Eq | Token::KwIn | Token::Semi
                    )
            }) {
                j += 1;
            }
            if let Some(delim) = self.tokens.get(j) {
                return constraint_from_source(&self.text, constraint_start..delim.span.start);
            }
        }
        while self.tokens.get(j).is_some_and(|token| {
            token.span.start < end
                && !matches!(
                    token.token,
                    Token::ColonEq | Token::Eq | Token::KwIn | Token::Semi
                )
        }) {
            j += 1;
        }
        if self
            .tokens
            .get(j)
            .is_some_and(|token| matches!(token.token, Token::ColonEq | Token::Eq))
        {
            infer_literal_constraint(self.tokens.get(j + 1).map(|token| &token.token))
        } else {
            None
        }
    }
}
