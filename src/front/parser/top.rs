use super::{ParseError, ParsedDef, Parser, TopLevel, UseTree, Visibility};
use crate::core::syntax::Term;
use crate::front::lexer::Token;

impl<'a, 'bump> Parser<'a, 'bump> {
    pub fn parse_program(&mut self) -> Result<Vec<TopLevel<'bump>>, ParseError> {
        let mut tops = Vec::new();
        while !self.is_at_end() {
            tops.push(self.parse_top_level()?);
        }
        Ok(tops)
    }

    pub fn parse_expr_top(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let t = self.parse_expr()?;
        if !self.is_at_end() {
            return Err(ParseError {
                message: "unexpected tokens after expression".into(),
                span: self.current_span(),
            });
        }
        Ok(t)
    }

    pub fn parse_def_top(&mut self) -> Result<ParsedDef<'bump>, ParseError> {
        self.parse_def()
    }

    fn parse_top_level(&mut self) -> Result<TopLevel<'bump>, ParseError> {
        while self.peek_token() == Some(Token::Newline) {
            self.advance();
        }
        let start_span = self.current_span();

        let visibility = if self.peek_token() == Some(Token::KwPub) {
            self.advance();
            Visibility::Public
        } else {
            Visibility::Private
        };

        if self.peek_token() == Some(Token::KwUse) {
            let uses = self.parse_use_trees()?;
            return Ok(TopLevel::TLUse(uses, visibility, start_span));
        }

        if self.peek_token() == Some(Token::KwMod) {
            self.advance();
            let name = self.parse_ident()?;
            let top = TopLevel::TLMod(name, start_span.clone());
            return Ok(self.with_visibility(top, visibility));
        }

        if self.peek_token() == Some(Token::KwExtern) {
            self.advance();
            let (name, params, ret) = self.parse_extern_def()?;
            let top = TopLevel::TLExternDef(name, params, ret, start_span);
            return Ok(self.with_visibility(top, visibility));
        }

        if self.peek_token() == Some(Token::KwInstance) {
            let (name, constraint, value) = self.parse_instance()?;
            let top = TopLevel::TLInstance(name, constraint, value, start_span);
            return Ok(self.with_visibility(top, visibility));
        }

        if self.peek_token() == Some(Token::KwTheorem) {
            self.advance();
            let name = self.parse_ident()?;
            let prop = if self.try_expect(&Token::Colon) {
                self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::ColonEq))?
            } else {
                self.arena.builtin(self.pool.intern("data"))
            };
            self.expect(&Token::ColonEq)?;
            let body = self.parse_expr()?;
            let top = TopLevel::TLTheorem(name, prop, body, start_span);
            return Ok(self.with_visibility(top, visibility));
        }

        if self.peek_token() == Some(Token::KwDef) {
            let (name, params, m_ret, body) = self.parse_def()?;
            let top = TopLevel::TLDef(name, params, m_ret, body, start_span);
            return Ok(self.with_visibility(top, visibility));
        }

        if matches!(visibility, Visibility::Public) {
            return Err(ParseError {
                message: "`pub` may only prefix `def`, `instance`, `theorem`, `use`, or `mod`"
                    .into(),
                span: start_span,
            });
        }

        if self.peek_token() == Some(Token::HashCheck) {
            self.advance();
            let split = self.find_check_constraint_colon();
            let (term, constraint) = if let Some(split) = split {
                let term = self.parse_expr_until(|_, i| i == split)?;
                self.expect(&Token::Colon)?;
                (term, self.parse_expr()?)
            } else {
                (
                    self.parse_expr()?,
                    self.arena.builtin(self.pool.intern("data")),
                )
            };
            let (term, constraint) = if let Term::Annot(t, c) = term {
                (*t, *c)
            } else {
                (term, constraint)
            };
            return Ok(TopLevel::TLCheck(term, constraint, start_span));
        }

        if self.peek_token() == Some(Token::HashEval) {
            self.advance();
            return Ok(TopLevel::TLEval(self.parse_expr()?, start_span));
        }

        Ok(TopLevel::TLExpr(self.parse_expr()?, start_span))
    }

    fn find_check_constraint_colon(&self) -> Option<usize> {
        let mut parens = 0usize;
        let mut braces = 0usize;
        let mut last = None;
        let mut i = self.pos;
        while i < self.tokens.len() {
            match self.tokens[i].0 {
                Token::LParen => parens += 1,
                Token::RParen => parens = parens.saturating_sub(1),
                Token::LBrace => braces += 1,
                Token::RBrace => braces = braces.saturating_sub(1),
                Token::KwDef
                | Token::HashCheck
                | Token::HashEval
                | Token::KwTheorem
                | Token::KwPub
                | Token::KwUse
                | Token::KwMod
                | Token::KwExtern
                | Token::KwInstance
                    if parens == 0 && braces == 0 =>
                {
                    break;
                }
                Token::Colon if parens == 0 && braces == 0 => last = Some(i),
                _ => {}
            }
            i += 1;
        }
        last
    }

    fn parse_use_trees(&mut self) -> Result<&'bump [UseTree<'bump>], ParseError> {
        self.expect(&Token::KwUse)?;
        let mut imports = Vec::new();
        loop {
            let mut path = Vec::new();
            path.push(self.parse_ident()?);
            loop {
                if !self.try_expect(&Token::PathSep) {
                    break;
                }
                if self.peek_token() == Some(Token::LBrace) {
                    self.advance();
                    let prefix = path.clone();
                    loop {
                        let leaf = self.parse_ident()?;
                        let mut full = prefix.clone();
                        full.push(leaf);
                        let alias = if self.try_expect(&Token::KwAs) {
                            Some(self.parse_ident()?)
                        } else {
                            None
                        };
                        imports.push(UseTree {
                            path: self.arena.alloc_slice(&full),
                            alias,
                        });
                        if !self.try_expect(&Token::Comma) {
                            break;
                        }
                    }
                    self.expect(&Token::RBrace)?;
                    path.clear();
                    break;
                }
                path.push(self.parse_ident()?);
            }
            if path.is_empty() {
                if !self.try_expect(&Token::Comma) {
                    break;
                }
                continue;
            }
            let alias = if self.try_expect(&Token::KwAs) {
                Some(self.parse_ident()?)
            } else {
                None
            };
            imports.push(UseTree {
                path: self.arena.alloc_slice(&path),
                alias,
            });
            if !self.try_expect(&Token::Comma) {
                break;
            }
        }
        Ok(self.arena.alloc_slice(&imports))
    }

    fn with_visibility(&self, top: TopLevel<'bump>, visibility: Visibility) -> TopLevel<'bump> {
        match visibility {
            Visibility::Private => top,
            Visibility::Public => TopLevel::TLPublic(self.bump_alloc_top(top)),
        }
    }

    fn bump_alloc_top(&self, top: TopLevel<'bump>) -> &'bump TopLevel<'bump> {
        self.arena.bump().alloc(top)
    }
}
