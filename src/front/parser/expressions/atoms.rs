use super::*;

impl<'a, 'bump> Parser<'a, 'bump> {
    fn parse_head(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let term = self.parse_atom()?;
        self.apply_suffixes(term)
    }

    pub(super) fn builtin(&self, name: &str) -> &'bump Term<'bump> {
        self.arena.builtin(self.pool.intern(name))
    }

    fn apply_suffixes(
        &mut self,
        mut t: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        loop {
            if self.peek_token().is_some_and(Self::is_expr_terminator) {
                break;
            }

            let changed = if self.peek_token() == Some(Token::KwWhere) {
                t = self.parse_refine_suffix(t)?;
                true
            } else if self.peek_token() == Some(Token::Colon) {
                if let Some(c) = self.try_parse(Token::Colon, |s| {
                    s.parse_expr_until(|tokens, i| {
                        matches!(tokens[i].0, Token::KwBy | Token::ColonEq | Token::RParen)
                    })
                }) {
                    t = self.arena.annot(t, c);
                    true
                } else {
                    false
                }
            } else if self.peek_token() == Some(Token::KwBy) {
                if let Some(tactics) = self.parse_by_proof_clause() {
                    t = self.arena.by_proof(Some(t), tactics);
                    true
                } else {
                    false
                }
            } else if self.peek_token() == Some(Token::Dot) {
                self.advance();
                let field = self.parse_ident()?;
                if let Term::Builtin(base_name) | Term::Named(base_name) = t
                    && Self::is_namespace_like_prefix(base_name)
                {
                    if field
                        .chars()
                        .next()
                        .is_some_and(|ch| ch.is_ascii_uppercase())
                    {
                        return Err(ParseError {
                            message: "enum variant access uses `::` instead of `.`".into(),
                            span: self.current_span(),
                        });
                    }
                    let dotted = self.pool.intern(&format!("{}.{}", base_name, field));
                    t = self.arena.named(dotted);
                } else {
                    t = self.arena.method_call(t, field);
                }
                true
            } else if self.peek_token() == Some(Token::LBrace) {
                if let Term::Builtin(name) | Term::Named(name) | Term::Global(name) = t {
                    t = self.parse_named_struct_cons(Some(*name))?;
                    true
                } else {
                    false
                }
            } else {
                false
            };
            if !changed {
                break;
            }
        }
        Ok(t)
    }

    fn is_namespace_like_prefix(name: &str) -> bool {
        name.contains("::")
            || name.contains('.')
            || name
                .chars()
                .next()
                .is_some_and(|ch| ch.is_ascii_uppercase())
    }

    pub(super) fn parse_expr_bp(&mut self, min_prec: u8) -> Result<&'bump Term<'bump>, ParseError> {
        let mut lhs = self.parse_head()?;

        while let Some(tok) = self.peek_token() {
            if Self::is_expr_terminator(tok.clone()) {
                break;
            }

            if let Some((prec, assoc)) = Self::infix_bp(&tok) {
                if prec < min_prec {
                    break;
                }
                if tok == Token::Slash && self.peek_ahead_is(&Token::Eq) {
                    break;
                }
                self.advance();
                let rbp = match assoc {
                    Associativity::Left => prec + 1,
                    Associativity::Right => prec,
                    Associativity::None => prec + 1,
                };

                if tok == Token::ThinArrow {
                    let rhs = self.parse_expr_bp(rbp)?;
                    lhs = self.arena.pi(self.pool.intern(""), lhs, rhs);
                } else {
                    let op = Self::token_to_primop(&tok);
                    let rhs = self.parse_expr_bp(rbp)?;
                    lhs = self
                        .arena
                        .app(self.arena.app(self.arena.prim_op(op), lhs), rhs);
                }
                continue;
            }

            if min_prec <= PREC_APP && Self::is_atom_start(&tok) {
                match self.parse_head() {
                    Ok(arg) => {
                        lhs = self.arena.app(lhs, arg);
                        continue;
                    }
                    Err(_) => break,
                }
            }

            break;
        }
        Ok(lhs)
    }

    fn parse_refine_suffix(
        &mut self,
        parent: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwWhere)?;
        self.expect(&Token::LParen)?;
        let param_name = self.parse_ident()?;
        self.expect(&Token::FatArrow)?;
        let predicate = self.parse_expr()?;
        self.expect(&Token::RParen)?;
        Ok(self.arena.refine(param_name, parent, predicate))
    }

    fn parse_atom(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::IntLit(n)) => {
                self.advance();
                Ok(self.arena.lit_int(n))
            }
            Some(Token::StrLit(s)) => {
                self.advance();
                let name = self.pool.intern(&s);
                Ok(self.arena.lit_str(name))
            }
            Some(Token::True) => {
                self.advance();
                Ok(self.arena.lit_bool(true))
            }
            Some(Token::False) => {
                self.advance();
                Ok(self.arena.lit_bool(false))
            }
            Some(Token::AndIntro) => {
                self.advance();
                Ok(self.builtin(AND_INTRO))
            }
            Some(Token::AndElimLeft) => {
                self.advance();
                Ok(self.builtin(AND_ELIM_LEFT))
            }
            Some(Token::And) => {
                self.advance();
                Ok(self.builtin(BUILTIN_AND))
            }
            Some(Token::Or) => {
                self.advance();
                Ok(self.builtin(BUILTIN_OR))
            }
            Some(Token::Not) => {
                self.advance();
                Ok(self.builtin(BUILTIN_NOT))
            }
            Some(Token::Implies) => {
                self.advance();
                Ok(self.builtin(BUILTIN_IMPLIES))
            }
            Some(Token::KwTheorem) => {
                self.advance();
                Ok(self.builtin(BUILTIN_THEOREM))
            }
            Some(Token::KwExact) | Some(Token::KwApply) | Some(Token::KwIntro)
            | Some(Token::KwHave) => self.parse_var(),
            Some(Token::KwAuto) => {
                self.advance();
                Ok(self.arena.auto_proof())
            }
            Some(Token::Ident(_)) => self.parse_var(),
            Some(Token::Dollar) => self.parse_splice(),
            Some(Token::KwFun) => self.parse_fun_lam(),
            Some(Token::KwDo) => self.parse_do_expr(),
            Some(Token::KwUnsafe) => self.parse_unsafe_expr(),
            Some(Token::KwPure) => self.parse_pure_expr(),
            Some(Token::Minus) => {
                self.advance();
                let t = self.parse_atom()?;
                Ok(self.arena.app(
                    self.arena
                        .app(self.arena.prim_op(PrimOp::Sub), self.arena.lit_int(0)),
                    t,
                ))
            }
            Some(Token::LParen) => self.parse_parens(),
            Some(Token::LBrace) => self.parse_named_struct_cons(None),
            Some(Token::KwBy) => {
                self.advance();
                let tactics = self.parse_tactics()?;
                Ok(self.arena.by_proof(None, tactics))
            }
            Some(tok) => {
                let span = self.peek().map(|(_, s)| s.clone()).unwrap_or(0..0);
                Err(ParseError {
                    message: format!("unexpected token {:?}", tok),
                    span,
                })
            }
            None => Err(ParseError {
                message: "unexpected EOF".into(),
                span: 0..0,
            }),
        }
    }

    fn parse_var(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let name = self.parse_path_ident()?;
        if name == "quote" {
            self.expect(&Token::LBrace)?;
            let inner = self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::RBrace))?;
            self.expect(&Token::RBrace)?;
            return Ok(self.arena.quote(inner));
        }
        if KEYWORDS.contains(&name)
            && !matches!(
                name,
                BUILTIN_DATA | BUILTIN_PROP | BUILTIN_THEOREM | BUILTIN_PROOF
            )
        {
            Err(ParseError {
                message: format!("keyword '{}' cannot be used as identifier", name),
                span: self.current_span(),
            })
        } else if BUILTIN_NAMES.contains(&name) {
            Ok(self.arena.builtin(name))
        } else {
            Ok(self.arena.named(name))
        }
    }

    fn parse_splice(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::Dollar)?;
        self.expect(&Token::LParen)?;
        let inner = self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::RParen))?;
        self.expect(&Token::RParen)?;
        Ok(self.arena.splice(inner))
    }

    pub(crate) fn parse_path_ident(&mut self) -> Result<Name<'bump>, ParseError> {
        let first = self.parse_decl_ident()?;
        let mut parts = vec![first];
        while self.try_expect(&Token::PathSep) {
            parts.push(self.parse_ident()?);
        }
        if parts.len() == 1 {
            return Ok(first);
        }
        Ok(self.pool.intern(&parts.join("::")))
    }

    pub(super) fn parse_variant_name(&mut self) -> Result<Name<'bump>, ParseError> {
        let name = self.parse_path_ident()?;
        if self.peek_token() == Some(Token::Dot) {
            let span = self.peek().map(|(_, span)| span.clone()).unwrap_or(0..0);
            return Err(ParseError {
                message: "enum variant paths use `::` instead of `.`".into(),
                span,
            });
        }
        Ok(name)
    }

    pub(crate) fn parse_ident(&mut self) -> Result<Name<'bump>, ParseError> {
        match self.peek() {
            Some((Token::Ident(name), _)) => {
                let n = self.pool.intern(name);
                self.advance();
                Ok(n)
            }
            Some((t, span)) => Err(ParseError {
                message: format!("expected identifier, found {:?}", t),
                span: span.clone(),
            }),
            None => Err(ParseError {
                message: "expected identifier, found EOF".into(),
                span: 0..0,
            }),
        }
    }

    pub(crate) fn parse_decl_ident(&mut self) -> Result<Name<'bump>, ParseError> {
        match self.peek() {
            Some((Token::Ident(name), _)) => {
                let n = self.pool.intern(name);
                self.advance();
                Ok(n)
            }
            Some((Token::KwExact, _)) => {
                self.advance();
                Ok(self.pool.intern(TACTIC_EXACT))
            }
            Some((Token::KwApply, _)) => {
                self.advance();
                Ok(self.pool.intern(TACTIC_APPLY))
            }
            Some((Token::KwIntro, _)) => {
                self.advance();
                Ok(self.pool.intern(TACTIC_INTRO))
            }
            Some((Token::KwHave, _)) => {
                self.advance();
                Ok(self.pool.intern(TACTIC_HAVE))
            }
            Some((t, span)) => Err(ParseError {
                message: format!("expected identifier, found {:?}", t),
                span: span.clone(),
            }),
            None => Err(ParseError {
                message: "expected identifier, found EOF".into(),
                span: 0..0,
            }),
        }
    }

    fn parse_fun_lam(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.advance();
        let params = self.parse_many_fun_params()?;
        self.expect(&Token::FatArrow)?;
        let body = self.parse_expr()?;
        let func_body = params
            .iter()
            .rfold(body, |b, &(pn, _)| self.arena.named_lam(pn, b));
        let default = self.builtin(BUILTIN_DATA);
        let func_constraint = params.iter().rfold(default, |b, &(pn, mc)| {
            self.arena.pi(pn, mc.unwrap_or(default), b)
        });
        Ok(self.arena.annot(func_body, func_constraint))
    }

    fn parse_many_fun_params(
        &mut self,
    ) -> Result<Vec<(Name<'bump>, Option<&'bump Term<'bump>>)>, ParseError> {
        let mut params = Vec::new();
        loop {
            match self.peek_token() {
                Some(Token::FatArrow) | None => break,
                Some(Token::LParen | Token::LBrace) => {
                    if let Some(group) = self.parse_param_group()? {
                        params.extend(group);
                    }
                }
                Some(Token::Ident(_)) => {
                    let pname = self.parse_ident()?;
                    params.push((pname, None));
                }
                _ => break,
            }
        }
        if params.is_empty() {
            return Err(ParseError {
                message: "fun expression must have at least one parameter".into(),
                span: self.current_span(),
            });
        }
        Ok(params)
    }

    fn parse_parens(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::LParen)?;
        if self.try_expect(&Token::RParen) {
            return Ok(self.builtin(BUILTIN_UNIT));
        }
        let t = self.parse_expr()?;
        self.expect(&Token::RParen)?;
        Ok(t)
    }

    fn parse_named_struct_cons(
        &mut self,
        name: Option<Name<'bump>>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::LBrace)?;
        let mut fields = Vec::new();
        loop {
            if self.try_expect(&Token::RBrace) {
                break;
            }
            let field = self.parse_ident()?;
            self.expect(&Token::ColonEq)?;
            let value = self.parse_expr()?;
            fields.push((field, value));
            if self.try_expect(&Token::Comma) {
                continue;
            }
            self.expect(&Token::RBrace)?;
            break;
        }
        if fields.is_empty() {
            return Err(ParseError {
                message: "struct initializer must have at least one field".into(),
                span: self.current_span(),
            });
        }
        Ok(self
            .arena
            .named_struct_cons(name, self.arena.alloc_slice(&fields)))
    }
}
