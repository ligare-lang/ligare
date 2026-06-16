#[allow(dead_code)]
use logos::Logos;

use bumpalo::Bump;

use crate::core::pool::{StringPool, TermArena};
use crate::core::syntax::{Name, PrimOp, Term};
use crate::front::lexer::Token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopLevel<'bump> {
    TLDef(Name<'bump>, &'bump Term<'bump>),
    TLCheck(&'bump Term<'bump>, &'bump Term<'bump>),
    TLShow(&'bump Term<'bump>),
    TLExpr(&'bump Term<'bump>),
}

const KEYWORDS: &[&str] = &[
    "let", "in", "if", "then", "else", "true", "false", "by", "func", "where", "def", "auto",
];

type SpannedToken = (Token, std::ops::Range<usize>);

pub struct Parser<'a, 'bump> {
    tokens: &'a [SpannedToken],
    pos: usize,
    pool: &'a StringPool<'bump>,
    arena: &'a TermArena<'bump>,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: std::ops::Range<usize>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} at {}..{}",
            self.message, self.span.start, self.span.end
        )
    }
}

impl std::error::Error for ParseError {}

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

    fn peek(&self) -> Option<&SpannedToken> {
        self.tokens.get(self.pos)
    }

    fn peek_token(&self) -> Option<Token> {
        self.peek().map(|(t, _)| t.clone())
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn expect(&mut self, expected: &Token) -> Result<(), ParseError> {
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

    fn try_expect(&mut self, expected: &Token) -> bool {
        if self.peek_token().as_ref() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn is_at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    // ── Top-level ──

    pub fn parse_program(&mut self) -> Result<Vec<TopLevel<'bump>>, ParseError> {
        let mut tops = Vec::new();
        while !self.is_at_end() {
            tops.push(self.parse_top_level()?);
        }
        Ok(tops)
    }

    pub fn parse_expr_top(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let t = self.parse_expr(&[])?;
        if !self.is_at_end() {
            return Err(ParseError {
                message: "unexpected tokens after expression".into(),
                span: 0..0,
            });
        }
        Ok(t)
    }

    pub fn parse_def_top(&mut self) -> Result<(Name<'bump>, &'bump Term<'bump>), ParseError> {
        self.parse_def()
    }

    fn parse_top_level(&mut self) -> Result<TopLevel<'bump>, ParseError> {
        if self.peek_token() == Some(Token::KwDef) {
            let (name, term) = self.parse_def()?;
            return Ok(TopLevel::TLDef(name, term));
        }
        if self.peek_token() == Some(Token::HashCheck) {
            self.advance();
            let term = self.parse_expr(&[])?;
            let constraint: &'bump Term<'bump> = if self.try_expect(&Token::Colon) {
                self.parse_expr(&[])?
            } else {
                self.arena.builtin(self.pool.intern("data"))
            };
            return Ok(TopLevel::TLCheck(term, constraint));
        }
        if self.peek_token() == Some(Token::HashShow) {
            self.advance();
            let term = self.parse_expr(&[])?;
            return Ok(TopLevel::TLShow(term));
        }
        let term = self.parse_expr(&[])?;
        Ok(TopLevel::TLExpr(term))
    }

    // ── Expressions (with annotation / no-annotation) ──

    fn parse_app_no_annot(
        &mut self,
        env: &[Name<'bump>],
    ) -> Result<&'bump Term<'bump>, ParseError> {
        self.parse_app_generic(env, |s, e| s.parse_term_no_annot(e))
    }

    fn parse_app_generic(
        &mut self,
        env: &[Name<'bump>],
        parse_term_fn: impl Fn(&mut Self, &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        if let Ok(t) = self.parse_let_expr(env) {
            return Ok(t);
        }
        if let Ok(t) = self.parse_func_expr(env) {
            return Ok(t);
        }
        if let Ok(t) = self.parse_dep_arrow_expr() {
            return Ok(t);
        }
        let t1 = parse_term_fn(self, env)?;
        let mut result = t1;
        loop {
            // If the next token is an infix operator, break so that
            // parse_binop_rhs handles it. This prevents unary minus
            // from being parsed greedily inside the application loop
            // when it should be a binary operator (e.g., "n-1").
            if let Some(tok) = self.peek_token()
                && Self::token_precedence(&tok).is_some()
            {
                break;
            }
            match parse_term_fn(self, env) {
                Ok(t) => result = self.arena.app(result, t),
                Err(_) => break,
            }
        }
        Ok(result)
    }

    fn parse_term_no_annot(
        &mut self,
        env: &[Name<'bump>],
    ) -> Result<&'bump Term<'bump>, ParseError> {
        let t = self.parse_atom(env)?;
        self.parse_refine_only(t)
    }

    fn parse_refine_only(
        &mut self,
        t: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        match self.try_parse_refine_suffix(t) {
            Ok(t2) => self.parse_refine_only(t2),
            Err(_) => Ok(t),
        }
    }

    // ── Definitions ──

    fn parse_def(&mut self) -> Result<(Name<'bump>, &'bump Term<'bump>), ParseError> {
        self.expect(&Token::KwDef)?;
        let name = self.parse_ident()?;
        let params = self.parse_many_curried_params();
        let m_ret = self.parse_type_annotation(&[]);
        self.expect(&Token::ColonEq)?;

        let param_names: Vec<Name<'bump>> = params.iter().map(|(n, _)| *n).collect();
        let env: Vec<Name<'bump>> = param_names.iter().rev().copied().collect();
        let body = self.parse_expr(&env)?;
        let body = subst_this(self.arena, name, body);

        let func_body = params.iter().fold(body, |b, _| self.arena.lam(b));
        let result = match m_ret {
            Some(c) => self.arena.annot(func_body, c),
            None => func_body,
        };
        Ok((name, result))
    }

    fn parse_curried_param(&mut self) -> Option<(Name<'bump>, Option<&'bump Term<'bump>>)> {
        if !self.try_expect(&Token::LParen) {
            return None;
        }
        let pname = match self.parse_ident() {
            Ok(n) => n,
            Err(_) => return None,
        };
        let mconstr = self.parse_type_annotation(&[]);
        if !self.try_expect(&Token::RParen) {
            return None;
        }
        Some((pname, mconstr))
    }

    fn parse_many_curried_params(&mut self) -> Vec<(Name<'bump>, Option<&'bump Term<'bump>>)> {
        let mut params = Vec::new();
        while let Some(p) = self.parse_curried_param() {
            params.push(p);
        }
        params
    }

    // ── Expressions ──

    fn parse_expr(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        if let Ok(t) = self.parse_if_expr(env) {
            return Ok(t);
        }
        self.parse_operators(env, false)
    }

    fn parse_if_expr(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        if !self.try_expect(&Token::KwIf) {
            return Err(ParseError {
                message: "not an if expression".into(),
                span: 0..0,
            });
        }
        let cond = self.parse_expr(env)?;
        self.expect(&Token::KwThen)?;
        let tbranch = self.parse_expr(env)?;
        self.expect(&Token::KwElse)?;
        let fbranch = self.parse_expr(env)?;
        Ok(self.arena.if_then_else(cond, tbranch, fbranch))
    }

    fn parse_operators(
        &mut self,
        env: &[Name<'bump>],
        no_annot: bool,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        let app = if no_annot {
            self.parse_app_no_annot(env)?
        } else {
            self.parse_app(env)?
        };
        self.parse_binop_rhs(env, app, 0, no_annot)
    }

    fn parse_app(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        self.parse_app_generic(env, |s, e| s.parse_term(e))
    }

    // ── Let ──

    fn parse_let_expr(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        if !self.try_expect(&Token::KwLet) {
            return Err(ParseError {
                message: "not a let expression".into(),
                span: 0..0,
            });
        }
        let name = self.parse_ident()?;
        let m_constraint = self.parse_type_annotation(env);
        let m_proof = self.parse_by_proof_clause(env);
        self.expect(&Token::ColonEq)?;
        let val = self.parse_expr(env)?;
        let val = match m_proof {
            Some(p) => self.arena.by_proof(val, p),
            None => val,
        };
        self.expect(&Token::KwIn)?;
        let mut extended_env: Vec<Name<'bump>> = vec![name];
        extended_env.extend_from_slice(env);
        let body = self.parse_expr(&extended_env)?;
        Ok(self.arena.let_(name, val, body, m_constraint))
    }

    /// Attempt to consume `tok` then run `parse_fn`. On failure, restore position.
    fn try_parse<T>(
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

    fn parse_type_annotation(&mut self, env: &[Name<'bump>]) -> Option<&'bump Term<'bump>> {
        self.try_parse(Token::Colon, |s| s.parse_expr(env))
    }

    fn parse_by_proof_clause(&mut self, env: &[Name<'bump>]) -> Option<&'bump Term<'bump>> {
        self.try_parse(Token::KwBy, |s| s.parse_term(env))
    }

    // ── Func ──

    fn parse_func_expr(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        if !self.try_expect(&Token::KwFunc) {
            return Err(ParseError {
                message: "not a func expression".into(),
                span: 0..0,
            });
        }
        let fname = self.parse_ident()?;
        let params = self.parse_many_curried_params();
        let m_ret = self.parse_type_annotation(env);
        self.expect(&Token::ColonEq)?;

        let param_names: Vec<Name<'bump>> = params.iter().map(|(n, _)| *n).collect();
        let mut extended_env: Vec<Name<'bump>> = param_names.iter().rev().copied().collect();
        extended_env.extend_from_slice(env);
        let body = self.parse_expr(&extended_env)?;
        let body = subst_this(self.arena, fname, body);

        let params_slice = self.arena.alloc_slice(&params);
        Ok(self.arena.func(fname, params_slice, m_ret, &[], &[], body))
    }

    // ── Dependent arrow: (x : A) -> B ──

    fn parse_dep_arrow_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let saved = self.pos;
        if !self.try_expect(&Token::LParen) {
            return Err(ParseError {
                message: "not a dep arrow".into(),
                span: 0..0,
            });
        }
        let x = match self.parse_ident() {
            Ok(n) => n,
            Err(_) => {
                self.pos = saved;
                return Err(ParseError {
                    message: "not a dep arrow".into(),
                    span: 0..0,
                });
            }
        };
        if !self.try_expect(&Token::Colon) {
            self.pos = saved;
            return Err(ParseError {
                message: "not a dep arrow".into(),
                span: 0..0,
            });
        }
        let a = match self.parse_expr(&[]) {
            Ok(t) => t,
            Err(_) => {
                self.pos = saved;
                return Err(ParseError {
                    message: "not a dep arrow".into(),
                    span: 0..0,
                });
            }
        };
        if !self.try_expect(&Token::RParen) {
            self.pos = saved;
            return Err(ParseError {
                message: "not a dep arrow".into(),
                span: 0..0,
            });
        }
        if !self.try_expect(&Token::ThinArrow) {
            self.pos = saved;
            return Err(ParseError {
                message: "not a dep arrow".into(),
                span: 0..0,
            });
        }
        let b = self.parse_expr(&[x])?;
        Ok(self.arena.pi(x, a, b))
    }

    // ── Term ──

    fn parse_term(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        let t = self.parse_atom(env)?;
        self.parse_suffixes(env, t)
    }

    fn parse_suffixes(
        &mut self,
        env: &[Name<'bump>],
        t: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        match self.try_parse_refine_suffix(t) {
            Ok(t2) => self.parse_suffixes(env, t2),
            Err(_) => match self.try_parse(Token::Colon, |s| s.parse_expr(env)) {
                Some(c) => self.parse_suffixes(env, self.arena.annot(t, c)),
                None => Ok(t),
            },
        }
    }

    // ── Atom ──

    fn parse_atom(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::IntLit(n)) => {
                self.advance();
                Ok(self.arena.lit_int(n))
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
                Ok(self.arena.builtin(self.pool.intern("∧-intro")))
            }
            Some(Token::AndElimLeft) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("∧-elim-left")))
            }
            Some(Token::And) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("and")))
            }
            Some(Token::Or) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("or")))
            }
            Some(Token::Not) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("not")))
            }
            Some(Token::Implies) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("implies")))
            }
            Some(Token::KwAuto) => {
                self.advance();
                Ok(self.arena.auto_proof())
            }
            Some(Token::Ident(_)) => self.parse_var(env),
            Some(Token::Backslash) | Some(Token::Lambda) => self.parse_lam(env),
            Some(Token::Minus) => {
                self.advance();
                let t = self.parse_atom(env)?;
                let sub_call = self
                    .arena
                    .app(self.arena.prim_op(PrimOp::Sub), self.arena.lit_int(0));
                Ok(self.arena.app(sub_call, t))
            }
            Some(Token::LParen) => self.parse_parens(env),
            Some(Token::LBrace) => {
                self.advance();
                let t = self.parse_expr(env)?;
                self.expect(&Token::RBrace)?;
                Ok(self.arena.proof_block(t))
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

    fn parse_var(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        let name = self.parse_ident()?;
        if let Some(i) = env.iter().position(|n| *n == name) {
            Ok(self.arena.var(i))
        } else if KEYWORDS.contains(&name) {
            Err(ParseError {
                message: format!("keyword '{}' cannot be used as identifier", name),
                span: 0..0,
            })
        } else {
            Ok(self.arena.builtin(name))
        }
    }

    fn parse_ident(&mut self) -> Result<Name<'bump>, ParseError> {
        match self.peek() {
            Some((Token::Ident(name), _)) => {
                let interned = self.pool.intern(name);
                self.advance();
                Ok(interned)
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

    fn parse_lam(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::Backslash) | Some(Token::Lambda) => self.advance(),
            _ => {
                return Err(ParseError {
                    message: "expected lambda".into(),
                    span: 0..0,
                });
            }
        };
        let x = self.parse_ident()?;
        self.expect(&Token::Dot)?;
        let mut extended_env: Vec<Name<'bump>> = vec![x];
        extended_env.extend_from_slice(env);
        let body = self.parse_expr(&extended_env)?;
        Ok(self.arena.lam(body))
    }

    fn parse_parens(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::LParen)?;
        let t = self.parse_expr(env)?;
        self.expect(&Token::RParen)?;
        Ok(t)
    }

    // ── Refinement ──

    fn try_parse_refine_suffix(
        &mut self,
        parent: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        if !self.try_expect(&Token::KwWhere) {
            return Err(ParseError {
                message: "not a refinement".into(),
                span: 0..0,
            });
        }
        self.expect(&Token::LParen)?;
        let param_name = self.parse_ident()?;
        self.expect(&Token::FatArrow)?;
        let predicate = self.parse_expr(&[param_name])?;
        self.expect(&Token::RParen)?;
        let pred2 = replace_var_zero(self.arena, predicate);
        Ok(self.arena.refine(self.pool.intern(""), parent, pred2))
    }

    // ── Operator precedence (Pratt-style) ──

    fn token_precedence(tok: &Token) -> Option<(i32, Associativity)> {
        match tok {
            Token::Star | Token::Slash | Token::Percent => Some((4, Associativity::Left)),
            Token::ThinArrow => Some((3, Associativity::Right)),
            Token::Plus | Token::Minus => Some((2, Associativity::Left)),
            Token::Eq
            | Token::Le
            | Token::Ge
            | Token::Neq
            | Token::Lt
            | Token::Gt
            | Token::EqEq => Some((1, Associativity::None)),
            _ => None,
        }
    }

    fn parse_binop_rhs(
        &mut self,
        env: &[Name<'bump>],
        mut lhs: &'bump Term<'bump>,
        min_prec: i32,
        no_annot: bool,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        while let Some(tok) = self.peek_token()
            && let Some((prec, assoc)) = Self::token_precedence(&tok)
            && prec >= min_prec
        {
            let next_min = match assoc {
                Associativity::Left => prec + 1,
                Associativity::Right => prec,
                Associativity::None => prec + 1,
            };

            // Handle arrow separately (different AST node)
            if tok == Token::ThinArrow {
                self.advance();
                let rhs_atom = self.parse_app_any(env, no_annot)?;
                let rhs = self.parse_binop_rhs(env, rhs_atom, next_min, no_annot)?;
                return Ok(self.arena.pi(self.pool.intern(""), lhs, rhs));
            }

            // Guard / against /=
            if tok == Token::Slash && self.peek_ahead_is(&Token::Eq) {
                break;
            }

            self.advance();
            let op = match &tok {
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
            };

            let rhs_atom = self.parse_app_any(env, no_annot)?;
            let rhs = self.parse_binop_rhs(env, rhs_atom, next_min, no_annot)?;
            let op_app = self.arena.app(self.arena.prim_op(op), lhs);
            lhs = self.arena.app(op_app, rhs);
        }
        Ok(lhs)
    }

    fn parse_app_any(
        &mut self,
        env: &[Name<'bump>],
        no_annot: bool,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        if no_annot {
            self.parse_app_no_annot(env)
        } else {
            self.parse_app(env)
        }
    }

    fn peek_ahead_is(&self, tok: &Token) -> bool {
        self.tokens
            .get(self.pos + 1)
            .map(|(t, _)| t == tok)
            .unwrap_or(false)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Associativity {
    Left,
    Right,
    None,
}

// ── Helper functions ──

pub fn replace_var_zero<'bump>(
    arena: &TermArena<'bump>,
    term: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    match term {
        Term::Var(0) => arena.ref_param(),
        Term::App(f, a) => {
            let f2 = replace_var_zero(arena, f);
            let a2 = replace_var_zero(arena, a);
            arena.app(f2, a2)
        }
        Term::Lam(b) => {
            let b2 = replace_var_zero(arena, b);
            arena.lam(b2)
        }
        Term::Let(n, v, b, mc) => {
            let v2 = replace_var_zero(arena, v);
            let b2 = replace_var_zero(arena, b);
            let mc2 = mc.map(|c| replace_var_zero(arena, c));
            arena.let_(n, v2, b2, mc2)
        }
        Term::IfThenElse(c, t, f) => {
            let c2 = replace_var_zero(arena, c);
            let t2 = replace_var_zero(arena, t);
            let f2 = replace_var_zero(arena, f);
            arena.if_then_else(c2, t2, f2)
        }
        Term::Annot(inner, c) => {
            let inner2 = replace_var_zero(arena, inner);
            let c2 = replace_var_zero(arena, c);
            arena.annot(inner2, c2)
        }
        Term::ByProof(inner, p) => {
            let inner2 = replace_var_zero(arena, inner);
            let p2 = replace_var_zero(arena, p);
            arena.by_proof(inner2, p2)
        }
        _ => term,
    }
}

pub fn subst_this<'bump>(
    arena: &TermArena<'bump>,
    name: Name<'bump>,
    term: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    match term {
        Term::Builtin(n) if *n == name => arena.this_(),
        Term::App(f, a) => {
            let f2 = subst_this(arena, name, f);
            let a2 = subst_this(arena, name, a);
            arena.app(f2, a2)
        }
        Term::Lam(b) => {
            let b2 = subst_this(arena, name, b);
            arena.lam(b2)
        }
        Term::Pi(x, a, b) => {
            let a2 = subst_this(arena, name, a);
            let b2 = subst_this(arena, name, b);
            arena.pi(x, a2, b2)
        }
        Term::Let(x, v, b, mc) => {
            let v2 = subst_this(arena, name, v);
            let b2 = subst_this(arena, name, b);
            let mc2 = mc.map(|c| subst_this(arena, name, c));
            arena.let_(x, v2, b2, mc2)
        }
        Term::IfThenElse(c, t, f) => {
            let c2 = subst_this(arena, name, c);
            let t2 = subst_this(arena, name, t);
            let f2 = subst_this(arena, name, f);
            arena.if_then_else(c2, t2, f2)
        }
        Term::Annot(inner, c) => {
            let inner2 = subst_this(arena, name, inner);
            let c2 = subst_this(arena, name, c);
            arena.annot(inner2, c2)
        }
        Term::ByProof(inner, p) => {
            let inner2 = subst_this(arena, name, inner);
            let p2 = subst_this(arena, name, p);
            arena.by_proof(inner2, p2)
        }
        Term::Refine(n, par, p) => {
            let par2 = subst_this(arena, name, par);
            let p2 = subst_this(arena, name, p);
            arena.refine(n, par2, p2)
        }
        Term::Func(fn_name, params, m_ret, pre, post, body) => {
            let params2 = params
                .iter()
                .map(|(n, mc)| {
                    let mc2 = mc.map(|c| subst_this(arena, name, c));
                    (*n, mc2)
                })
                .collect::<Vec<_>>();
            let params_slice = arena.alloc_slice(&params2);
            let m_ret2 = m_ret.map(|c| subst_this(arena, name, c));
            let pre2: Vec<_> = pre.iter().map(|t| *subst_this(arena, name, t)).collect();
            let pre_slice = arena.alloc_slice(&pre2);
            let post2: Vec<_> = post.iter().map(|t| *subst_this(arena, name, t)).collect();
            let post_slice = arena.alloc_slice(&post2);
            let body2 = subst_this(arena, name, body);
            arena.func(fn_name, params_slice, m_ret2, pre_slice, post_slice, body2)
        }
        Term::ProofBlock(t) => {
            let t2 = subst_this(arena, name, t);
            arena.proof_block(t2)
        }
        _ => term,
    }
}

// ── Public entry points ──

pub fn parse_expr_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    let lex = Token::lexer(input);
    let tokens: Vec<SpannedToken> = lex
        .spanned()
        .filter_map(|(r, s)| r.ok().map(|t| (t, s)))
        .collect();
    let pool = StringPool::new(bump);
    let mut parser = Parser::new(&tokens, &pool, arena);
    parser.parse_expr_top().map_err(|e| e.to_string())
}

pub fn parse_def_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<(Name<'bump>, &'bump Term<'bump>), String> {
    let lex = Token::lexer(input);
    let tokens: Vec<SpannedToken> = lex
        .spanned()
        .filter_map(|(r, s)| r.ok().map(|t| (t, s)))
        .collect();
    let pool = StringPool::new(bump);
    let mut parser = Parser::new(&tokens, &pool, arena);
    parser.parse_def_top().map_err(|e| e.to_string())
}

pub fn parse_program<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<Vec<TopLevel<'bump>>, String> {
    let lex = Token::lexer(input);
    let tokens: Vec<SpannedToken> = lex
        .spanned()
        .filter_map(|(r, s)| r.ok().map(|t| (t, s)))
        .collect();
    let pool = StringPool::new(bump);
    let mut parser = Parser::new(&tokens, &pool, arena);
    parser.parse_program().map_err(|e| e.to_string())
}
