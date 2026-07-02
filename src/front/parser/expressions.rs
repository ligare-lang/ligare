use super::{
    Associativity, BUILTIN_NAMES, KEYWORDS, ParseError, ParsedMatchBranch, Parser, SpannedToken,
};
use crate::config::{
    AND_ELIM_LEFT, AND_INTRO, BUILTIN_AND, BUILTIN_DATA, BUILTIN_IMPLIES, BUILTIN_NOT, BUILTIN_OR,
    BUILTIN_PROOF, BUILTIN_PROP, BUILTIN_THEOREM, BUILTIN_UNIT,
};
use crate::core::syntax::{DoStmt, Name, PrimOp, Term};
use crate::front::lexer::Token;
use std::cmp::Ordering;

const PREC_COMPARISON: u8 = 2;
const PREC_ADD_SUB: u8 = 3;
const PREC_ARROW: u8 = 4;
const PREC_MUL_DIV_MOD: u8 = 5;
const PREC_APP: u8 = PREC_MUL_DIV_MOD + 1;

const TACTIC_EXACT: &str = "exact";
const TACTIC_APPLY: &str = "apply";
const TACTIC_INTRO: &str = "intro";
const TACTIC_HAVE: &str = "have";

impl<'a, 'bump> Parser<'a, 'bump> {
    pub(super) fn parse_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        if self.peek_token().is_some_and(Self::is_expr_terminator) {
            return Err(ParseError {
                message: "expected expression before terminator".into(),
                span: self.current_span(),
            });
        }

        match self.peek_token() {
            Some(Token::KwIf) => self.parse_if_expr(),
            Some(Token::KwMatch) => self.parse_match_expr(),
            Some(Token::KwLet) => self.parse_let_expr(),
            Some(Token::KwDo) => self.parse_do_expr(),
            Some(Token::KwUnsafe) => self.parse_unsafe_expr(),
            Some(Token::KwPure) => self.parse_pure_expr(),
            Some(Token::KwFunc) => self.parse_func_expr(),
            Some(Token::LParen) => {
                let saved = self.pos;
                if let Ok(t) = self.parse_dep_arrow_expr() {
                    return Ok(t);
                }
                self.pos = saved;
                self.parse_expr_bp(0)
            }
            _ => self.parse_expr_bp(0),
        }
    }

    pub(super) fn parse_expr_until<F>(
        &mut self,
        is_delim: F,
    ) -> Result<&'bump Term<'bump>, ParseError>
    where
        F: FnMut(&[SpannedToken], usize) -> bool,
    {
        let start = self.pos;
        let end = self.find_expr_boundary(is_delim);
        if end == start {
            return Err(ParseError {
                message: "expected expression before delimiter".into(),
                span: self.current_span(),
            });
        }

        let mut sub = Parser::new(&self.tokens[start..end], self.pool, self.arena);
        let term = sub.parse_expr_top()?;
        self.pos = end;
        Ok(term)
    }

    fn find_expr_boundary<F>(&self, mut is_delim: F) -> usize
    where
        F: FnMut(&[SpannedToken], usize) -> bool,
    {
        let mut i = self.pos;
        let mut parens = 0usize;
        let mut braces = 0usize;
        while i < self.tokens.len() {
            match self.tokens[i].0 {
                Token::LParen => parens += 1,
                Token::RParen => {
                    if parens == 0 && braces == 0 && is_delim(self.tokens, i) {
                        break;
                    }
                    parens = parens.saturating_sub(1);
                }
                Token::LBrace => braces += 1,
                Token::RBrace => {
                    if parens == 0 && braces == 0 && is_delim(self.tokens, i) {
                        break;
                    }
                    braces = braces.saturating_sub(1);
                }
                _ if parens == 0 && braces == 0 && is_delim(self.tokens, i) => break,
                _ => {}
            }
            i += 1;
        }
        i
    }

    fn parse_if_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwIf)?;
        let cond = self.parse_expr()?;
        self.expect(&Token::KwThen)?;
        let tbranch = self.parse_expr()?;
        self.expect(&Token::KwElse)?;
        Ok(self.arena.if_then_else(cond, tbranch, self.parse_expr()?))
    }

    fn parse_match_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwMatch)?;
        let scrutinee = self.parse_expr()?;
        self.expect(&Token::KwWith)?;
        let mut branches: Vec<ParsedMatchBranch<'bump>> = Vec::new();
        loop {
            if !self.try_expect(&Token::Bar) {
                break;
            }
            let variant_name = self.parse_ident()?;
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

    fn parse_let_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
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

    fn parse_do_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
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
        let m_constraint = self.parse_constraint_annotation();
        self.expect(&Token::ColonEq)?;
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

    fn parse_let_destruct(
        &mut self,
        struct_name: Name<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        let mut field_names: Vec<Name<'bump>> = Vec::new();
        loop {
            let fname = self.parse_ident()?;
            field_names.push(fname);
            if !self.try_expect(&Token::Comma) {
                break;
            }
        }
        self.expect(&Token::RBrace)?;
        if field_names.is_empty() {
            return Err(ParseError {
                message: "destructuring pattern must have at least one field".into(),
                span: self.current_span(),
            });
        }
        let _m_constraint = self.parse_constraint_annotation();
        self.expect(&Token::ColonEq)?;
        let val = self.parse_expr()?;
        self.expect(&Token::KwIn)?;
        let mut body = self.parse_expr()?;
        for fname in field_names.iter().rev() {
            let proj_name = self.pool.intern(&format!("{}.{}", struct_name, fname));
            let proj = self.arena.app(self.arena.named(proj_name), val);
            body = self.arena.let_(fname, proj, body, None);
        }
        Ok(body)
    }

    fn parse_func_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwFunc)?;
        let name = self.parse_ident()?;
        let (params, m_ret, body) = self.parse_func_body(name)?;
        Ok(self.desugar_def(name, &params, m_ret, body))
    }

    fn parse_unsafe_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwUnsafe)?;
        self.expect(&Token::LBrace)?;
        let inner = self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::RBrace))?;
        self.expect(&Token::RBrace)?;
        Ok(self.arena.unsafe_(inner))
    }

    fn parse_pure_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwPure)?;
        let inner = self.parse_expr()?;
        Ok(self.arena.pure(inner))
    }

    fn parse_dep_arrow_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::LParen)?;
        let x = self.parse_ident()?;
        self.expect(&Token::Colon)?;
        let a = self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::RParen))?;
        self.expect(&Token::RParen)?;
        self.expect(&Token::ThinArrow)?;
        let b = self.parse_expr()?;
        Ok(self.arena.pi(x, a, b))
    }

    fn infix_bp(tok: &Token) -> Option<(u8, Associativity)> {
        match tok {
            Token::Star | Token::Slash | Token::Percent => {
                Some((PREC_MUL_DIV_MOD, Associativity::Left))
            }
            Token::ThinArrow => Some((PREC_ARROW, Associativity::Right)),
            Token::Plus | Token::Minus => Some((PREC_ADD_SUB, Associativity::Left)),
            Token::Eq
            | Token::Le
            | Token::Ge
            | Token::Neq
            | Token::Lt
            | Token::Gt
            | Token::EqEq => Some((PREC_COMPARISON, Associativity::None)),
            _ => None,
        }
    }

    fn is_atom_start(tok: &Token) -> bool {
        matches!(
            tok,
            Token::IntLit(_)
                | Token::StrLit(_)
                | Token::True
                | Token::False
                | Token::Ident(_)
                | Token::Backslash
                | Token::Lambda
                | Token::KwFun
                | Token::LParen
                | Token::Minus
                | Token::KwAuto
                | Token::KwDo
                | Token::KwPure
                | Token::KwUnsafe
                | Token::AndIntro
                | Token::AndElimLeft
                | Token::And
                | Token::Or
                | Token::Not
                | Token::Implies
                | Token::KwBy
        )
    }

    fn token_to_primop(tok: &Token) -> PrimOp {
        match tok {
            Token::Star => PrimOp::Mul,
            Token::Slash => PrimOp::Div,
            Token::Percent => PrimOp::Mod_,
            Token::Plus => PrimOp::Add,
            Token::Minus => PrimOp::Sub,
            Token::Eq | Token::EqEq => PrimOp::Eq,
            Token::Le => PrimOp::Le,
            Token::Ge => PrimOp::Ge,
            Token::Neq => PrimOp::Neq,
            Token::Lt => PrimOp::Lt,
            Token::Gt => PrimOp::Gt,
            _ => unreachable!(),
        }
    }

    pub(super) fn is_expr_terminator(tok: Token) -> bool {
        matches!(
            tok,
            Token::ColonEq
                | Token::KwIn
                | Token::KwThen
                | Token::KwElse
                | Token::RParen
                | Token::RBrace
                | Token::Comma
                | Token::Semi
                | Token::Bar
        )
    }

    pub(super) fn is_tactic_arg_delim(tokens: &[SpannedToken], i: usize) -> bool {
        matches!(
            tokens[i].0,
            Token::ColonEq
                | Token::KwIn
                | Token::KwThen
                | Token::KwElse
                | Token::RParen
                | Token::RBrace
                | Token::Colon
                | Token::Semi
                | Token::KwDef
                | Token::HashCheck
                | Token::HashEval
        )
    }

    pub(super) fn is_struct_field_constraint_delim(tokens: &[SpannedToken], i: usize) -> bool {
        if matches!(
            tokens[i].0,
            Token::KwDef
                | Token::KwExtern
                | Token::KwInstance
                | Token::KwTheorem
                | Token::KwPub
                | Token::KwUse
                | Token::KwMod
                | Token::HashGlobalAllocator
                | Token::HashCheck
                | Token::HashEval
                | Token::ColonEq
        ) {
            return true;
        }
        if let Token::Ident(_) = tokens[i].0 {
            return tokens.get(i + 1).is_some_and(|(t, _)| *t == Token::Colon);
        }
        false
    }

    fn parse_head(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let term = self.parse_atom()?;
        self.apply_suffixes(term)
    }

    fn builtin(&self, name: &str) -> &'bump Term<'bump> {
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
            } else if self.peek_token() == Some(Token::Dot)
                && matches!(t, Term::Builtin(_) | Term::Named(_))
            {
                self.advance();
                let field = self.parse_ident()?;
                let base_name = match t {
                    Term::Builtin(n) | Term::Named(n) => n,
                    _ => unreachable!(),
                };
                let dotted = self.pool.intern(&format!("{}.{}", base_name, field));
                t = self.arena.named(dotted);
                true
            } else {
                false
            };
            if !changed {
                break;
            }
        }
        Ok(t)
    }

    fn parse_expr_bp(&mut self, min_prec: u8) -> Result<&'bump Term<'bump>, ParseError> {
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
            Some(Token::Backslash) | Some(Token::Lambda) => self.parse_lam(),
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
        let name = self.parse_decl_ident()?;
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

    pub(super) fn parse_ident(&mut self) -> Result<Name<'bump>, ParseError> {
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

    pub(super) fn parse_decl_ident(&mut self) -> Result<Name<'bump>, ParseError> {
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

    fn parse_lam(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::Backslash) | Some(Token::Lambda) => self.advance(),
            _ => {
                return Err(ParseError {
                    message: "expected lambda".into(),
                    span: 0..0,
                });
            }
        };
        let mut params = vec![self.parse_ident()?];
        while self
            .peek_token()
            .is_some_and(|t| matches!(t, Token::Ident(_)))
        {
            params.push(self.parse_ident()?);
        }
        self.expect(&Token::Dot)?;
        let body = self.parse_expr()?;
        Ok(params
            .into_iter()
            .rfold(body, |b, p| self.arena.named_lam(p, b)))
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
                Some(Token::LParen) => {
                    self.advance();
                    let pname = self.parse_ident()?;
                    let mconstr = self.parse_constraint_annotation();
                    self.expect(&Token::RParen)?;
                    params.push((pname, mconstr));
                }
                Some(Token::LBrace) => {
                    self.advance();
                    let pname = self.parse_ident()?;
                    let mconstr = self
                        .parse_constraint_annotation()
                        .map(|c| self.arena.implicit(c));
                    self.expect(&Token::RBrace)?;
                    params.push((pname, mconstr));
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
}
