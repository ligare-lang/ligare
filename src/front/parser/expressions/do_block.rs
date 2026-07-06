use super::*;

impl<'a, 'bump> Parser<'a, 'bump> {
    pub(super) fn parse_if_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwIf)?;
        let cond = self.parse_expr()?;
        self.expect(&Token::KwThen)?;
        let tbranch = self.parse_expr()?;
        self.expect(&Token::KwElse)?;
        Ok(self.arena.if_then_else(cond, tbranch, self.parse_expr()?))
    }

    pub(super) fn parse_match_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwMatch)?;
        let scrutinee = self.parse_expr()?;
        self.expect(&Token::KwWith)?;
        let mut branches: Vec<ParsedMatchBranch<'bump>> = Vec::new();
        loop {
            if !self.try_expect(&Token::Bar) {
                break;
            }
            let variant_name = self.parse_variant_name()?;
            let mut binds: Vec<(Name<'bump>, &'bump Term<'bump>)> = Vec::new();
            while self
                .peek_token()
                .is_some_and(|t| matches!(t, Token::Ident(_)))
            {
                let bind_name = self.parse_ident()?;
                let bind_ty = self.builtin(BUILTIN_DATA);
                binds.push((bind_name, bind_ty));
            }
            self.expect(&Token::FatArrow)?;
            let body = self.parse_expr()?;
            branches.push((variant_name, binds, body));
        }
        if branches.is_empty() {
            return Err(ParseError {
                message: "match expression must have at least one branch".into(),
                span: self.current_span(),
            });
        }
        let branches_slice: Vec<_> = branches
            .into_iter()
            .map(|(variant_name, b, body)| (variant_name, self.arena.alloc_slice(&b), body))
            .collect();
        Ok(self
            .arena
            .named_match(scrutinee, self.arena.alloc_slice(&branches_slice)))
    }

    pub(super) fn parse_let_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwLet)?;
        let name = self.parse_ident()?;
        if self.try_expect(&Token::LBrace) {
            return self.parse_let_destruct(name);
        }
        let m_constraint = self.parse_constraint_annotation();
        let m_proof = self.parse_by_proof_clause();
        self.expect(&Token::ColonEq)?;
        let val = self.parse_expr()?;
        let val = match m_proof {
            Some(tactics) => self.arena.by_proof(Some(val), tactics),
            None => val,
        };
        self.expect(&Token::KwIn)?;
        let body = self.parse_expr()?;
        Ok(self.arena.let_(name, val, body, m_constraint))
    }

    pub(super) fn parse_do_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwDo)?;
        if self.peek_token() == Some(Token::LBrace) {
            return self.parse_braced_do_expr();
        }

        self.parse_layout_do_expr()
    }

    fn parse_braced_do_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::LBrace)?;
        let mut stmts = Vec::new();
        while self.peek_token() == Some(Token::Semi) || self.peek_token() == Some(Token::Newline) {
            self.advance();
        }
        while self.peek_token() != Some(Token::RBrace) {
            if self.is_at_end() {
                return Err(ParseError {
                    message: "unterminated do block".into(),
                    span: self.current_span(),
                });
            }
            let stmt = if self.peek_token() == Some(Token::KwLet) {
                self.parse_do_let_stmt()?
            } else if self.peek_is_bind_stmt() {
                self.parse_do_bind_stmt()?
            } else {
                DoStmt::Expr(self.parse_expr_until(|tokens, i| {
                    matches!(tokens[i].0, Token::Semi | Token::RBrace)
                })?)
            };
            stmts.push(stmt);
            if self.try_expect(&Token::Semi) {
                while self.peek_token() == Some(Token::Semi)
                    || self.peek_token() == Some(Token::Newline)
                {
                    self.advance();
                }
            } else if self.peek_token() != Some(Token::RBrace) {
                return Err(ParseError {
                    message: "expected `;` or `}` in do block".into(),
                    span: self.current_span(),
                });
            }
        }
        self.expect(&Token::RBrace)?;
        if stmts.is_empty() {
            return Err(ParseError {
                message: "do block must have at least one statement".into(),
                span: self.current_span(),
            });
        }
        Ok(self.arena.do_(self.arena.alloc_slice(&stmts)))
    }

    fn parse_layout_do_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        if self.is_at_end() {
            return Err(ParseError {
                message: "do block must have at least one statement".into(),
                span: self.current_span(),
            });
        }

        let indent = self.current_token_column();
        let mut stmts = Vec::new();
        let mut require_aligned = false;

        loop {
            if self.is_at_end() {
                break;
            }

            if require_aligned {
                match self.current_column_cmp(indent) {
                    Some(Ordering::Less) => break,
                    Some(Ordering::Equal) => {}
                    Some(Ordering::Greater) => {
                        return Err(ParseError {
                            message: "unexpected indentation in do block".into(),
                            span: self.current_span(),
                        });
                    }
                    None => break,
                }
            }

            let stmt = if self.peek_token() == Some(Token::KwLet) {
                self.parse_layout_do_let_stmt(indent)?
            } else if self.peek_is_bind_stmt() {
                self.parse_layout_do_bind_stmt(indent)?
            } else {
                DoStmt::Expr(self.parse_expr_until(|tokens, i| {
                    Self::is_layout_do_stmt_delim(tokens, i, indent)
                })?)
            };
            stmts.push(stmt);

            match self.consume_layout_do_separator(indent)? {
                Some(aligned) => require_aligned = aligned,
                None => break,
            }
        }

        if stmts.is_empty() {
            return Err(ParseError {
                message: "do block must have at least one statement".into(),
                span: self.current_span(),
            });
        }
        Ok(self.arena.do_(self.arena.alloc_slice(&stmts)))
    }

    fn parse_do_let_stmt(&mut self) -> Result<DoStmt<'bump>, ParseError> {
        self.expect(&Token::KwLet)?;
        let name = self.parse_ident()?;
        let m_constraint = self.parse_constraint_until(|tokens, i| {
            matches!(
                tokens[i].0,
                Token::KwBy | Token::ColonEq | Token::Eq | Token::Semi | Token::RBrace
            )
        });
        if !(self.try_expect(&Token::ColonEq) || self.try_expect(&Token::Eq)) {
            return Err(ParseError {
                message: "expected `:=` or `=` in do let statement".into(),
                span: self.current_span(),
            });
        }
        let val =
            self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::Semi | Token::RBrace))?;
        Ok(DoStmt::Let(name, val, m_constraint))
    }

    fn parse_layout_do_let_stmt(&mut self, indent: usize) -> Result<DoStmt<'bump>, ParseError> {
        self.expect(&Token::KwLet)?;
        let name = self.parse_ident()?;
        let m_constraint = self.parse_constraint_until(|tokens, i| {
            matches!(
                tokens[i].0,
                Token::KwBy | Token::ColonEq | Token::Eq | Token::RParen
            )
        });
        if !(self.try_expect(&Token::ColonEq) || self.try_expect(&Token::Eq)) {
            return Err(ParseError {
                message: "expected `:=` or `=` in do let statement".into(),
                span: self.current_span(),
            });
        }
        let val =
            self.parse_expr_until(|tokens, i| Self::is_layout_do_stmt_delim(tokens, i, indent))?;
        Ok(DoStmt::Let(name, val, m_constraint))
    }

    fn parse_do_bind_stmt(&mut self) -> Result<DoStmt<'bump>, ParseError> {
        let name = self.parse_ident()?;
        self.expect(&Token::LeftArrow)?;
        let rhs =
            self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::Semi | Token::RBrace))?;
        Ok(DoStmt::Bind(name, rhs))
    }

    fn parse_layout_do_bind_stmt(&mut self, indent: usize) -> Result<DoStmt<'bump>, ParseError> {
        let name = self.parse_ident()?;
        self.expect(&Token::LeftArrow)?;
        let rhs =
            self.parse_expr_until(|tokens, i| Self::is_layout_do_stmt_delim(tokens, i, indent))?;
        Ok(DoStmt::Bind(name, rhs))
    }

    fn peek_is_bind_stmt(&self) -> bool {
        matches!(self.peek(), Some((Token::Ident(_), _)))
            && self
                .tokens
                .get(self.pos + 1)
                .is_some_and(|(t, _)| *t == Token::LeftArrow)
    }

    fn consume_layout_do_separator(&mut self, indent: usize) -> Result<Option<bool>, ParseError> {
        match self.tokens.get(self.pos).map(|(t, _)| t) {
            None => Ok(None),
            Some(Token::Semi) => {
                while matches!(self.tokens.get(self.pos), Some((Token::Semi, _))) {
                    self.pos += 1;
                }
                let mut saw_newline = false;
                while matches!(self.tokens.get(self.pos), Some((Token::Newline, _))) {
                    saw_newline = true;
                    self.pos += 1;
                }
                if self.is_at_end() {
                    return Ok(None);
                }
                if !saw_newline {
                    return Ok(Some(false));
                }
                match self.current_column_cmp(indent) {
                    Some(Ordering::Less) => Ok(None),
                    Some(Ordering::Equal) => Ok(Some(true)),
                    Some(Ordering::Greater) => Err(ParseError {
                        message: "unexpected indentation in do block".into(),
                        span: self.current_span(),
                    }),
                    None => Ok(None),
                }
            }
            Some(Token::Newline) => {
                while matches!(self.tokens.get(self.pos), Some((Token::Newline, _))) {
                    self.pos += 1;
                }
                if self.is_at_end() {
                    return Ok(None);
                }
                match self.current_column_cmp(indent) {
                    Some(Ordering::Less) => Ok(None),
                    Some(Ordering::Equal) => Ok(Some(true)),
                    Some(Ordering::Greater) => Err(ParseError {
                        message: "unexpected indentation in do block".into(),
                        span: self.current_span(),
                    }),
                    None => Ok(None),
                }
            }
            Some(_) => Err(ParseError {
                message: "expected newline or `;` in do block".into(),
                span: self.current_span(),
            }),
        }
    }

    fn current_token_column(&self) -> usize {
        Self::token_column(self.tokens, self.pos)
    }

    fn current_column_cmp(&self, indent: usize) -> Option<Ordering> {
        self.tokens
            .get(self.pos)
            .map(|_| self.current_token_column().cmp(&indent))
    }

    fn is_layout_do_stmt_delim(tokens: &[SpannedToken], i: usize, indent: usize) -> bool {
        if matches!(tokens[i].0, Token::Semi) {
            return true;
        }
        if !matches!(tokens[i].0, Token::Newline) {
            return false;
        }
        let Some(next) = Self::next_non_newline(tokens, i + 1) else {
            return true;
        };
        Self::token_column(tokens, next) <= indent
    }

    fn next_non_newline(tokens: &[SpannedToken], mut i: usize) -> Option<usize> {
        while matches!(tokens.get(i), Some((Token::Newline, _))) {
            i += 1;
        }
        tokens.get(i).map(|_| i)
    }

    fn token_column(tokens: &[SpannedToken], i: usize) -> usize {
        let start = tokens.get(i).map(|(_, span)| span.start).unwrap_or(0);
        let mut j = i;
        while j > 0 {
            j -= 1;
            if matches!(tokens[j].0, Token::Newline) {
                return start.saturating_sub(tokens[j].1.end);
            }
        }
        start
    }
}
