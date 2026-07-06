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

mod atoms;
mod do_block;

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

    pub(super) fn parse_unsafe_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
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
                | Token::LBrace
                | Token::Dollar
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
                | Token::KwTheorem
                | Token::KwPub
                | Token::KwUse
                | Token::KwMod
                | Token::KwNamespace
                | Token::HashLBracket
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
}
