use super::{Attribute, ParseError, ParsedDef, Parser, TopLevel, UseTree, Visibility};
use crate::config::{GLOBAL_ALLOCATOR_ATTR, GLOBAL_ALLOCATOR_NAME_PREFIX, INSTANCE_ATTR};
use crate::core::syntax::Term;
use crate::front::lexer::Token;

impl<'a, 'bump> Parser<'a, 'bump> {
    pub fn parse_program(&mut self) -> Result<Vec<TopLevel<'bump>>, ParseError> {
        let mut tops = Vec::new();
        loop {
            while self.peek_token() == Some(Token::Newline) {
                self.advance();
            }
            if self.is_at_end() {
                break;
            }
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
        let attrs = self.parse_attributes()?;
        while self.peek_token() == Some(Token::Newline) {
            self.advance();
        }
        let global_allocator_attr = attrs.iter().any(|attr| attr.is_name(GLOBAL_ALLOCATOR_ATTR));
        let instance_attr = attrs.iter().any(|attr| attr.is_name(INSTANCE_ATTR));

        let visibility = if self.peek_token() == Some(Token::KwPub) {
            self.advance();
            Visibility::Public
        } else {
            Visibility::Private
        };

        if global_allocator_attr && instance_attr {
            return Err(ParseError {
                message: format!(
                    "#[{GLOBAL_ALLOCATOR_ATTR}] cannot be combined with #[{INSTANCE_ATTR}]"
                ),
                span: start_span,
            });
        }

        if global_allocator_attr && self.peek_token() != Some(Token::KwDef) {
            return Err(ParseError {
                message: format!("#[{GLOBAL_ALLOCATOR_ATTR}] may only prefix `def`"),
                span: start_span,
            });
        }

        if instance_attr && self.peek_token() != Some(Token::KwDef) {
            return Err(ParseError {
                message: format!("#[{INSTANCE_ATTR}] may only prefix `def`"),
                span: start_span,
            });
        }

        if self.peek_token() == Some(Token::KwUse) {
            let uses = self.parse_use_trees()?;
            return Ok(self.with_attributes(
                TopLevel::TLUse(uses, visibility, start_span.clone()),
                &attrs,
                start_span,
            ));
        }

        if self.peek_token() == Some(Token::KwMod) {
            self.advance();
            let name = self.parse_ident()?;
            let top = TopLevel::TLMod(name, start_span.clone());
            let top = self.with_visibility(top, visibility);
            return Ok(self.with_attributes(top, &attrs, start_span));
        }

        if self.peek_token() == Some(Token::KwNamespace) {
            self.advance();
            let name = self.parse_ident()?;
            self.expect(&Token::LBrace)?;
            let mut tops = Vec::new();
            while self.peek_token() != Some(Token::RBrace) {
                if self.is_at_end() {
                    return Err(ParseError {
                        message: "unterminated namespace block".into(),
                        span: start_span.clone(),
                    });
                }
                tops.push(self.parse_top_level()?);
            }
            self.expect(&Token::RBrace)?;
            let top =
                TopLevel::TLNamespace(name, self.arena.bump().alloc_slice_clone(&tops), start_span);
            let top = self.with_visibility(top, visibility);
            return Ok(self.with_attributes(top, &attrs, self.current_span()));
        }

        if self.peek_token() == Some(Token::KwExtern) {
            self.advance();
            let (name, params, ret) = self.parse_extern_def()?;
            let top = TopLevel::TLExternDef(name, params, ret, start_span);
            let top = self.with_visibility(top, visibility);
            return Ok(self.with_attributes(top, &attrs, self.current_span()));
        }

        if self.peek_token() == Some(Token::KwVariable) {
            if matches!(visibility, Visibility::Public) {
                return Err(ParseError {
                    message: "`pub` may only prefix `def`, `theorem`, `use`, `mod`, or `namespace`"
                        .into(),
                    span: start_span,
                });
            }
            let params = self.parse_variable()?;
            return Ok(self.with_attributes(
                TopLevel::TLVariable(params, start_span.clone()),
                &attrs,
                start_span,
            ));
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
            let top = self.with_visibility(top, visibility);
            return Ok(self.with_attributes(top, &attrs, self.current_span()));
        }

        if self.peek_token() == Some(Token::KwDef) {
            let (name, params, m_ret, body) = self.parse_def()?;
            let name = if global_allocator_attr {
                let encoded = format!("{GLOBAL_ALLOCATOR_NAME_PREFIX}{name}");
                self.pool.intern(&encoded)
            } else {
                name
            };
            let top = if instance_attr {
                if !params.is_empty() {
                    return Err(ParseError {
                        message: format!("#[{INSTANCE_ATTR}] def cannot take parameters"),
                        span: start_span,
                    });
                }
                let Some(constraint) = m_ret else {
                    return Err(ParseError {
                        message: format!("#[{INSTANCE_ATTR}] def requires an explicit constraint"),
                        span: start_span,
                    });
                };
                TopLevel::TLInstance(name, constraint, body, start_span)
            } else {
                TopLevel::TLDef(name, params, m_ret, body, start_span)
            };
            let top = self.with_visibility(top, visibility);
            let attrs = self.filter_surface_attrs(&attrs);
            return Ok(self.with_attributes(top, &attrs, self.current_span()));
        }

        if self
            .peek()
            .is_some_and(|(token, _)| matches!(token, Token::Ident(name) if name == "instance"))
        {
            return Err(ParseError {
                message: "instance syntax was removed; use `#[instance] def <name> : <constraint> := <value>`".into(),
                span: start_span,
            });
        }

        if matches!(visibility, Visibility::Public) {
            return Err(ParseError {
                message: "`pub` may only prefix `def`, `theorem`, `use`, `mod`, or `namespace`"
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
            return Ok(self.with_attributes(
                TopLevel::TLCheck(term, constraint, start_span.clone()),
                &attrs,
                start_span,
            ));
        }

        if self.peek_token() == Some(Token::HashEval) {
            self.advance();
            let term = self.parse_expr()?;
            return Ok(self.with_attributes(
                TopLevel::TLEval(term, start_span.clone()),
                &attrs,
                start_span,
            ));
        }

        if self.peek_token() == Some(Token::Dollar) {
            let Term::Splice(inner) = self.parse_expr()? else {
                unreachable!("a top-level `$` expression parses as splice")
            };
            return Ok(self.with_attributes(
                TopLevel::TLSplice(inner, start_span.clone()),
                &attrs,
                start_span,
            ));
        }

        let term = self.parse_expr()?;
        Ok(self.with_attributes(
            TopLevel::TLExpr(term, start_span.clone()),
            &attrs,
            start_span,
        ))
    }

    fn parse_attributes(&mut self) -> Result<Vec<Attribute<'bump>>, ParseError> {
        let mut attrs = Vec::new();
        while self.peek_token() == Some(Token::HashLBracket) {
            self.advance();
            let mut path = vec![self.parse_ident()?];
            while self.try_expect(&Token::PathSep) {
                path.push(self.parse_ident()?);
            }
            let args = if self.try_expect(&Token::LParen) {
                let mut args = Vec::new();
                if self.peek_token() != Some(Token::RParen) {
                    loop {
                        args.push(self.parse_expr_until(|tokens, i| {
                            matches!(tokens[i].0, Token::Comma | Token::RParen)
                        })?);
                        if !self.try_expect(&Token::Comma) {
                            break;
                        }
                    }
                }
                self.expect(&Token::RParen)?;
                self.arena.alloc_slice(&args)
            } else {
                self.arena.alloc_slice(&[])
            };
            self.expect(&Token::RBracket)?;
            attrs.push(Attribute {
                path: self.arena.alloc_slice(&path),
                args,
            });
            while self.peek_token() == Some(Token::Newline) {
                self.advance();
            }
        }
        Ok(attrs)
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
                | Token::KwNamespace
                | Token::KwExtern
                | Token::KwVariable
                | Token::HashLBracket
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
                            wildcard: false,
                        });
                        if !self.try_expect(&Token::Comma) {
                            break;
                        }
                    }
                    self.expect(&Token::RBrace)?;
                    path.clear();
                    break;
                }
                if self.peek_token() == Some(Token::Star) {
                    self.advance();
                    imports.push(UseTree {
                        path: self.arena.alloc_slice(&path),
                        alias: None,
                        wildcard: true,
                    });
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
                wildcard: false,
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

    fn with_attributes(
        &self,
        top: TopLevel<'bump>,
        attrs: &[Attribute<'bump>],
        span: std::ops::Range<usize>,
    ) -> TopLevel<'bump> {
        if attrs.is_empty() {
            top
        } else {
            TopLevel::TLAttributed(
                self.arena.alloc_slice(attrs),
                self.bump_alloc_top(top),
                span,
            )
        }
    }

    fn filter_surface_attrs(&self, attrs: &[Attribute<'bump>]) -> Vec<Attribute<'bump>> {
        attrs
            .iter()
            .copied()
            .filter(|attr| !attr.is_name(INSTANCE_ATTR))
            .collect()
    }

    fn bump_alloc_top(&self, top: TopLevel<'bump>) -> &'bump TopLevel<'bump> {
        self.arena.bump().alloc(top)
    }
}
