use super::{ParseError, ParsedDef, ParsedFuncBody, Parser, SpannedToken};
use crate::core::syntax::{Name, Tactic, Term};
use crate::front::lexer::Token;

type ParamList<'bump> = &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)];
type ExternDef<'bump> = (Name<'bump>, ParamList<'bump>, &'bump Term<'bump>);
type ParamGroup<'bump> = Vec<(Name<'bump>, Option<&'bump Term<'bump>>)>;

impl<'a, 'bump> Parser<'a, 'bump> {
    pub(super) fn parse_def(&mut self) -> Result<ParsedDef<'bump>, ParseError> {
        self.expect(&Token::KwDef)?;
        let name = self.parse_decl_ident()?;
        let (params, m_ret, body) = self.parse_func_body(name)?;
        let params_slice = self.arena.alloc_slice(&params);
        Ok((name, params_slice, m_ret, body))
    }

    pub(super) fn parse_extern_def(&mut self) -> Result<ExternDef<'bump>, ParseError> {
        self.expect(&Token::KwDef)?;
        let name = self.parse_decl_ident()?;
        let params = self.parse_many_curried_params()?;
        let ret = self
            .parse_constraint_until(|tokens, i| {
                matches!(
                    tokens[i].0,
                    Token::KwDef
                        | Token::KwExtern
                        | Token::HashCheck
                        | Token::HashEval
                        | Token::HashLBracket
                        | Token::KwTheorem
                        | Token::KwPub
                        | Token::KwUse
                        | Token::KwMod
                        | Token::KwNamespace
                        | Token::KwVariable
                )
            })
            .ok_or_else(|| ParseError {
                message: "extern def requires an explicit return constraint".into(),
                span: self.current_span(),
            })?;
        Ok((name, self.arena.alloc_slice(&params), ret))
    }

    pub(super) fn parse_variable(
        &mut self,
    ) -> Result<&'bump [(Name<'bump>, Option<&'bump Term<'bump>>)], ParseError> {
        self.expect(&Token::KwVariable)?;
        let params = self.parse_many_curried_params()?;
        if params.is_empty() {
            return Err(ParseError {
                message: "variable requires at least one parameter group".into(),
                span: self.current_span(),
            });
        }
        let default = self.arena.builtin(self.pool.intern("data"));
        let params = params
            .into_iter()
            .map(|(name, constraint)| {
                let constraint = match constraint {
                    Some(Term::Implicit(_)) => constraint,
                    Some(constraint) => Some(self.arena.implicit(constraint)),
                    None => Some(self.arena.implicit(default)),
                };
                (name, constraint)
            })
            .collect::<Vec<_>>();
        Ok(self.arena.alloc_slice(&params))
    }

    pub(super) fn desugar_def(
        &self,
        _name: Name<'bump>,
        params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let func_body = params
            .iter()
            .rfold(body, |b, &(pn, _)| self.arena.named_lam(pn, b));
        let default = self.arena.builtin(self.pool.intern("data"));
        let ret = m_ret.unwrap_or(default);
        let func_constraint = params.iter().rev().fold(ret, |b, &(pn, mc)| {
            let dom = mc.unwrap_or(default);
            self.arena.pi(pn, dom, b)
        });
        self.arena.annot(func_body, func_constraint)
    }

    pub(super) fn parse_func_body(
        &mut self,
        name: Name<'bump>,
    ) -> Result<ParsedFuncBody<'bump>, ParseError> {
        let params = self.parse_many_curried_params()?;
        let m_ret = self.parse_constraint_until(|tokens, i| matches!(tokens[i].0, Token::ColonEq));
        self.expect(&Token::ColonEq)?;
        let body_expr = if self.peek_token() == Some(Token::KwEnum) {
            self.parse_enum_body(name)?
        } else if self.peek_token() == Some(Token::KwStruct) {
            self.parse_struct_body(name)?
        } else if matches!(self.peek_token(), Some(Token::KwDo | Token::KwMatch)) {
            self.parse_expr()?
        } else if self.peek_token() == Some(Token::KwUnsafe) {
            self.parse_unsafe_expr()?
        } else {
            self.parse_expr_until(Self::is_top_level_body_delim)?
        };
        Ok((params, m_ret, body_expr))
    }

    fn is_top_level_body_delim(tokens: &[SpannedToken], i: usize) -> bool {
        if matches!(
            tokens[i].0,
            Token::KwDef
                | Token::KwExtern
                | Token::HashCheck
                | Token::HashEval
                | Token::HashLBracket
                | Token::KwTheorem
                | Token::KwPub
                | Token::KwUse
                | Token::KwMod
                | Token::KwNamespace
                | Token::KwVariable
                | Token::RBrace
                | Token::Semi
                | Token::Newline
        ) {
            return true;
        }
        matches!(tokens[i].0, Token::Dollar)
            && (i == 0 || matches!(tokens[i.saturating_sub(1)].0, Token::Newline))
    }

    pub(super) fn parse_param_group(&mut self) -> Result<Option<ParamGroup<'bump>>, ParseError> {
        let implicit = if self.try_expect(&Token::LBrace) {
            true
        } else if self.try_expect(&Token::LParen) {
            false
        } else {
            return Ok(None);
        };

        let close = if implicit {
            Token::RBrace
        } else {
            Token::RParen
        };

        let mut names = Vec::new();
        loop {
            match self.peek_token() {
                Some(Token::Colon) => break,
                Some(tok) if tok == close => break,
                Some(_) => names.push(self.parse_decl_ident()?),
                None => {
                    return Err(ParseError {
                        message: format!("expected {:?}, found EOF", close),
                        span: self.current_span(),
                    });
                }
            }
        }

        if names.is_empty() {
            return Err(ParseError {
                message: "parameter group must have at least one parameter".into(),
                span: self.current_span(),
            });
        }

        let mconstr = self
            .parse_constraint_annotation()
            .map(|c| if implicit { self.arena.implicit(c) } else { c });
        self.expect(&close)?;

        Ok(Some(
            names.into_iter().map(|pname| (pname, mconstr)).collect(),
        ))
    }

    fn parse_many_curried_params(
        &mut self,
    ) -> Result<Vec<(Name<'bump>, Option<&'bump Term<'bump>>)>, ParseError> {
        let mut params = Vec::new();
        while let Some(group) = self.parse_param_group()? {
            params.extend(group);
        }
        Ok(params)
    }

    pub(super) fn parse_constraint_annotation(&mut self) -> Option<&'bump Term<'bump>> {
        self.parse_constraint_until(|tokens, i| {
            matches!(
                tokens[i].0,
                Token::KwBy | Token::ColonEq | Token::RParen | Token::RBrace
            )
        })
    }

    pub(super) fn parse_constraint_until<F>(&mut self, is_delim: F) -> Option<&'bump Term<'bump>>
    where
        F: FnMut(&[SpannedToken], usize) -> bool,
    {
        self.try_parse(Token::Colon, |s| s.parse_expr_until(is_delim))
    }

    pub(super) fn parse_struct_field_constraint(
        &mut self,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        self.parse_expr_until(Self::is_struct_field_constraint_delim)
    }

    pub(super) fn parse_tactic_arg(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.parse_expr_until(Self::is_tactic_arg_delim)
    }

    pub(super) fn parse_by_proof_clause(&mut self) -> Option<&'bump [Tactic<'bump>]> {
        self.try_parse(Token::KwBy, |s| s.parse_tactics())
    }

    fn parse_enum_body(&mut self, name: Name<'bump>) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwEnum)?;
        let mut variants: Vec<(Name<'bump>, Vec<(Name<'bump>, &'bump Term<'bump>)>)> = Vec::new();
        loop {
            if !self.try_expect(&Token::Bar) {
                break;
            }
            let vname = self.parse_ident()?;
            let fields: Vec<(Name<'bump>, &'bump Term<'bump>)> = if self.try_expect(&Token::KwOf) {
                let mut fs = Vec::new();
                loop {
                    if !self.try_expect(&Token::LParen) {
                        break;
                    }
                    let fname = self.parse_ident()?;
                    let fty = if self.try_expect(&Token::Colon) {
                        self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::RParen))?
                    } else {
                        self.arena.builtin(self.pool.intern("data"))
                    };
                    self.expect(&Token::RParen)?;
                    fs.push((fname, fty));
                }
                fs
            } else {
                Vec::new()
            };
            variants.push((vname, fields));
        }
        if variants.is_empty() {
            return Err(ParseError {
                message: "enum must have at least one variant".into(),
                span: self.current_span(),
            });
        }
        let variants_slice: Vec<_> = variants
            .into_iter()
            .map(|(vn, fs)| (vn, self.arena.alloc_slice(&fs)))
            .collect();
        Ok(self
            .arena
            .enum_def(name, self.arena.alloc_slice(&variants_slice)))
    }

    fn parse_struct_body(&mut self, name: Name<'bump>) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwStruct)?;
        let mut fields: Vec<(Name<'bump>, &'bump Term<'bump>)> = Vec::new();
        loop {
            let saved = self.pos;
            let fname = match self.parse_ident() {
                Ok(n) => n,
                Err(_) => {
                    self.pos = saved;
                    break;
                }
            };
            let fty = if self.try_expect(&Token::Colon) {
                self.parse_struct_field_constraint()?
            } else {
                self.arena.builtin(self.pool.intern("data"))
            };
            fields.push((fname, fty));
        }
        if fields.is_empty() {
            return Err(ParseError {
                message: "struct must have at least one field".into(),
                span: self.current_span(),
            });
        }
        Ok(self.arena.struct_def(name, self.arena.alloc_slice(&fields)))
    }

    pub(super) fn parse_tactics(&mut self) -> Result<&'bump [Tactic<'bump>], ParseError> {
        let mut tactics: Vec<Tactic<'bump>> = Vec::new();
        loop {
            match self.peek() {
                None
                | Some((Token::ColonEq, _))
                | Some((Token::KwIn, _))
                | Some((Token::KwThen, _))
                | Some((Token::KwElse, _))
                | Some((Token::RParen, _))
                | Some((Token::RBrace, _))
                | Some((Token::Colon, _))
                | Some((Token::KwDef, _))
                | Some((Token::HashCheck, _))
                | Some((Token::HashEval, _)) => break,
                _ => {}
            }
            let tactic = self.parse_tactic()?;
            tactics.push(tactic);
            if self.peek_token() == Some(Token::Semi) {
                self.advance();
            }
        }
        if tactics.is_empty() {
            return Err(ParseError {
                message: "Empty proof block".into(),
                span: self.current_span(),
            });
        }
        Ok(self.arena.alloc_slice(&tactics))
    }

    fn parse_tactic(&mut self) -> Result<Tactic<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::KwExact) => {
                self.advance();
                let t = self.parse_tactic_arg()?;
                Ok(Tactic::Exact(t))
            }
            Some(Token::KwApply) => {
                self.advance();
                let t = self.parse_tactic_arg()?;
                Ok(Tactic::Apply(t))
            }
            Some(Token::KwIntro) => {
                self.advance();
                let name = if let Some(Token::Ident(_)) = self.peek_token() {
                    Some(self.parse_ident()?)
                } else {
                    None
                };
                Ok(Tactic::Intro(name))
            }
            Some(Token::KwHave) => {
                self.advance();
                let name = self.parse_ident()?;
                self.expect(&Token::ColonEq)?;
                let t = self.parse_tactic_arg()?;
                Ok(Tactic::Have(name, t))
            }
            Some(Token::Ident(_))
                if self
                    .tokens
                    .get(self.pos + 1)
                    .is_some_and(|(tok, _)| *tok == Token::LParen) =>
            {
                let name = self.parse_path_ident()?;
                self.expect(&Token::LParen)?;
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
                Ok(Tactic::Custom(name, self.arena.alloc_slice(&args)))
            }
            _ => {
                let t = self.parse_tactic_arg()?;
                Ok(Tactic::Exact(t))
            }
        }
    }
}
