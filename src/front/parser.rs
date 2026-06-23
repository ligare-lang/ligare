use logos::Logos;

use bumpalo::Bump;

use crate::core::pool::{StringPool, TermArena};
use crate::core::syntax::{FuncDef, Name, PrimOp, Tactic, Term};
use crate::front::lexer::Token;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TopLevel<'bump> {
    TLDef(Name<'bump>, &'bump FuncDef<'bump>),
    TLTheorem(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    TLCheck(&'bump Term<'bump>, &'bump Term<'bump>),
    TLShow(&'bump Term<'bump>),
    TLExpr(&'bump Term<'bump>),
}

const KEYWORDS: &[&str] = &[
    "let", "in", "if", "then", "else", "true", "false", "by", "func", "where", "def", "auto",
    "theorem",
];

type SpannedToken = (Token, std::ops::Range<usize>);

pub struct Parser<'a, 'bump> {
    tokens: &'a [SpannedToken],
    pos: usize,
    pool: &'a StringPool<'bump>,
    arena: &'a TermArena<'bump>,
    /// When true, `parse_suffixes` skips the `by` suffix (used for
    /// parsing type annotations where `by` belongs to the outer context).
    no_by: bool,
    /// When true, `parse_suffixes` skips the `:` type-annotation suffix
    /// (used for `#check` so that `:` is reserved as the constraint separator).
    no_annot: bool,
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
            no_by: false,
            no_annot: false,
        }
    }

    fn peek(&self) -> Option<&SpannedToken> {
        let mut i = self.pos;
        loop {
            match self.tokens.get(i) {
                Some((Token::Newline, _)) => i += 1,
                other => return other,
            }
        }
    }
    fn peek_token(&self) -> Option<Token> {
        self.peek().map(|(t, _)| t.clone())
    }
    fn advance(&mut self) {
        // Skip any leading Newlines (to reach the current token that peek() would return)
        while matches!(self.tokens.get(self.pos), Some((Token::Newline, _))) {
            self.pos += 1;
        }
        // Skip past the current token
        self.pos += 1;
        // Then skip any following Newlines
        while matches!(self.tokens.get(self.pos), Some((Token::Newline, _))) {
            self.pos += 1;
        }
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

    /// Return the span of the current peek position, or `0..0` at EOF.
    fn current_span(&self) -> std::ops::Range<usize> {
        self.peek().map(|(_, s)| s.clone()).unwrap_or(0..0)
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
                span: self.current_span(),
            });
        }
        Ok(t)
    }

    pub fn parse_def_top(&mut self) -> Result<(Name<'bump>, &'bump FuncDef<'bump>), ParseError> {
        self.parse_def()
    }

    fn parse_top_level(&mut self) -> Result<TopLevel<'bump>, ParseError> {
        if self.peek_token() == Some(Token::KwTheorem) {
            self.advance();
            let name = self.parse_ident()?;
            let prop = if self.try_expect(&Token::Colon) {
                self.parse_expr(&[])?
            } else {
                self.arena.builtin(self.pool.intern("data"))
            };
            self.expect(&Token::ColonEq)?;
            let body = self.parse_expr(&[])?;
            return Ok(TopLevel::TLTheorem(name, prop, body));
        }
        if self.peek_token() == Some(Token::KwDef) {
            let (name, func_def) = self.parse_def()?;
            return Ok(TopLevel::TLDef(name, func_def));
        }
        if self.peek_token() == Some(Token::HashCheck) {
            self.advance();
            // Suppress `:` type-annotation suffix so that `:` is reserved
            // for the constraint separator (e.g. `#check s some_sth : str`).
            self.no_annot = true;
            let full_term = self.parse_expr(&[])?;
            self.no_annot = false;
            // If `parse_expr` already returned an annotation (from `:`),
            // split it; otherwise expect `:` and parse constraint.
            let (term, constraint) = if let Term::Annot(t, c) = full_term {
                (*t, *c)
            } else if self.try_expect(&Token::Colon) {
                (full_term, self.parse_expr(&[])?)
            } else {
                (full_term, self.arena.builtin(self.pool.intern("data")))
            };
            return Ok(TopLevel::TLCheck(term, constraint));
        }
        if self.peek_token() == Some(Token::HashShow) {
            self.advance();
            return Ok(TopLevel::TLShow(self.parse_expr(&[])?));
        }
        Ok(TopLevel::TLExpr(self.parse_expr(&[])?))
    }

    // ── Expressions ──

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
        let mut result = parse_term_fn(self, env)?;
        loop {
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

    fn parse_def(&mut self) -> Result<(Name<'bump>, &'bump FuncDef<'bump>), ParseError> {
        self.expect(&Token::KwDef)?;
        let name = self.parse_ident()?;
        Ok((name, self.parse_func_body(name, &[])?))
    }

    fn parse_func_body(
        &mut self,
        name: Name<'bump>,
        outer_env: &[Name<'bump>],
    ) -> Result<&'bump FuncDef<'bump>, ParseError> {
        let params = self.parse_many_curried_params();
        let m_ret = self.parse_type_annotation(outer_env);
        self.expect(&Token::ColonEq)?;
        // Check for union / struct body (zero-param definitions)
        let body_expr = if self.peek_token() == Some(Token::KwUnion) {
            self.parse_union_body(name)?
        } else if self.peek_token() == Some(Token::KwStruct) {
            self.parse_struct_body(name)?
        } else {
            let param_names: Vec<Name<'bump>> = params.iter().map(|(n, _)| *n).collect();
            let mut env: Vec<Name<'bump>> = param_names.iter().rev().copied().collect();
            env.extend_from_slice(outer_env);
            self.parse_expr(&env)?
        };
        // All self-references stay as Builtin(name) — the evaluator
        // injects the self-reference at beta-reduction time.
        let body = body_expr;
        let params_slice = self.arena.alloc_slice(&params);
        let func_def = FuncDef {
            name,
            params: params_slice,
            ret: m_ret,
            body,
        };
        Ok(self.arena.bump().alloc(func_def))
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
        if let Ok(t) = self.parse_match_expr(env) {
            return Ok(t);
        }
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
        Ok(self
            .arena
            .if_then_else(cond, tbranch, self.parse_expr(env)?))
    }

    fn parse_match_expr(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        if !self.try_expect(&Token::KwMatch) {
            return Err(ParseError {
                message: "not a match expression".into(),
                span: 0..0,
            });
        }
        let scrutinee = self.parse_expr(env)?;
        self.expect(&Token::KwWith)?;
        // Parse branches: `| Pattern => body` repeated
        let mut branches: Vec<(
            usize,
            Vec<(Name<'bump>, &'bump Term<'bump>)>,
            &'bump Term<'bump>,
        )> = Vec::new();
        loop {
            if !self.try_expect(&Token::Bar) {
                break;
            }
            let _variant_name = self.parse_ident()?;
            // Parse optional bindings: `name1 name2 ...` (stop at `=>` or end)
            let mut binds: Vec<(Name<'bump>, &'bump Term<'bump>)> = Vec::new();
            while self
                .peek_token()
                .map_or(false, |t| matches!(t, Token::Ident(_)))
            {
                let bind_name = self.parse_ident()?;
                // Infer constraint as `data` for bindings
                let bind_ty = self.arena.builtin(self.pool.intern("data"));
                binds.push((bind_name, bind_ty));
            }
            self.expect(&Token::FatArrow)?;
            // Build extended env with bindings
            let mut ext_env: Vec<Name<'bump>> = binds.iter().map(|(n, _)| *n).collect();
            ext_env.extend_from_slice(env);
            let body = self.parse_expr(&ext_env)?;
            // Use variant name as index placeholder — real index resolved during check
            let idx = branches.len();
            branches.push((idx, binds, body));
        }
        if branches.is_empty() {
            return Err(ParseError {
                message: "match expression must have at least one branch".into(),
                span: self.current_span(),
            });
        }
        let branches_slice: Vec<_> = branches
            .into_iter()
            .map(|(idx, b, body)| (idx, self.arena.alloc_slice(&b), body))
            .collect();
        Ok(self
            .arena
            .match_(scrutinee, self.arena.alloc_slice(&branches_slice)))
    }

    /// Parse a union body: `union\n  | Variant1 of (x : Type)\n  | Variant2 ...`
    fn parse_union_body(&mut self, name: Name<'bump>) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwUnion)?;
        let mut variants: Vec<(Name<'bump>, Vec<(Name<'bump>, &'bump Term<'bump>)>)> = Vec::new();
        loop {
            if !self.try_expect(&Token::Bar) {
                break;
            }
            let vname = self.parse_ident()?;
            // Parse optional payload: `of (field1 : Type1) (field2 : Type2)`
            let fields: Vec<(Name<'bump>, &'bump Term<'bump>)> = if self.try_expect(&Token::KwOf) {
                let mut fs = Vec::new();
                // Parse one or more `(name : type)` pairs
                loop {
                    if !self.try_expect(&Token::LParen) {
                        break;
                    }
                    let fname = self.parse_ident()?;
                    let fty = if self.try_expect(&Token::Colon) {
                        self.parse_expr(&[])?
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
                message: "union must have at least one variant".into(),
                span: self.current_span(),
            });
        }
        let variants_slice: Vec<_> = variants
            .into_iter()
            .map(|(vn, fs)| (vn, self.arena.alloc_slice(&fs)))
            .collect();
        Ok(self
            .arena
            .union_def(name, self.arena.alloc_slice(&variants_slice)))
    }

    /// Parse a struct body: `struct\n  field1 : Type1\n  field2 : Type2`
    fn parse_struct_body(&mut self, name: Name<'bump>) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwStruct)?;
        let mut fields: Vec<(Name<'bump>, &'bump Term<'bump>)> = Vec::new();
        // Parse indented fields: each field is `name : type` (the `:` is optional).
        // Use `parse_term_no_annot` for field types to avoid greedy application
        // that would consume the next field name as an argument.
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
                self.parse_term_no_annot(&[])?
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
        // Check for destructuring: `let Name{field1, field2, ...} := val in body`
        if self.try_expect(&Token::LBrace) {
            return self.parse_let_destruct(env, name);
        }
        let m_constraint = self.parse_type_annotation(env);
        let m_proof = self.parse_by_proof_clause(env);
        self.expect(&Token::ColonEq)?;
        let val = self.parse_expr(env)?;
        let val = match m_proof {
            Some(tactics) => self.arena.by_proof(Some(val), tactics),
            None => val,
        };
        self.expect(&Token::KwIn)?;
        let mut extended_env: Vec<Name<'bump>> = vec![name];
        extended_env.extend_from_slice(env);
        let body = self.parse_expr(&extended_env)?;
        Ok(self.arena.let_(name, val, body, m_constraint))
    }

    /// Parse destructuring let: `let Name{field1, field2, ...} := val in body`
    /// Desugars to nested `let field1 := Name.field1 val in let field2 := ... in body`
    fn parse_let_destruct(
        &mut self,
        env: &[Name<'bump>],
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
        // Optional type annotation on the whole struct value
        let _m_constraint = self.parse_type_annotation(env);
        self.expect(&Token::ColonEq)?;
        let val = self.parse_expr(env)?;
        self.expect(&Token::KwIn)?;
        // Build nested let bindings.
        // Desugar `let Point{x, y} := val in body` to:
        //   let x := Point.x val in let y := Point.y val in body
        // where each inner `val` has its De Bruijn indices shifted by 1.

        // First, extend the env with ALL field names and parse the body.
        // Execution order: `let x := ... in let y := ... in body`
        // means the execution stack is [y, x, pt] (y at index 0).
        // So build env in the same order: innermost first.
        let mut ext_env: Vec<Name<'bump>> = env.to_vec();
        for fname in field_names.iter() {
            ext_env.insert(0, fname);
        }
        let mut body = self.parse_expr(&ext_env)?;

        // Then wrap with lets, outermost first (not reversed).
        // The field_names are in declaration order [x, y].
        // Build all projections first to avoid borrowing conflicts.
        let arena = self.arena;
        let mut projs: Vec<&'bump Term<'bump>> = Vec::new();
        for (i, fname) in field_names.iter().enumerate() {
            let dotted = self.pool.intern(&format!("{}.{}", struct_name, fname));
            // val starts at index 0; each wrapping shifts it by i
            let val_shifted = if i == 0 {
                val
            } else {
                // Manual shift: add i to all De Bruijn indices in val
                let shift = i as i32;
                arena.map(val, &move |t| {
                    if let Term::Var(j) = t {
                        Some(arena.var((*j as i32 + shift) as usize))
                    } else {
                        None
                    }
                })
            };
            let proj = arena.app(arena.builtin(dotted), val_shifted);
            projs.push(proj);
        }
        // Now build nested lets using the projections.
        // Iterate in reverse so that the first-declared field (e.g. x)
        // is the outermost let, matching the De Bruijn shifts computed
        // above and the ext_env order used when parsing the body.
        for (fname, proj) in field_names.iter().rev().zip(projs.iter().rev()) {
            body = arena.let_(fname, proj, body, None);
        }
        Ok(body)
    }

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
        self.no_by = true;
        let result = self.try_parse(Token::Colon, |s| s.parse_expr(env));
        self.no_by = false;
        result
    }

    fn parse_by_proof_clause(&mut self, env: &[Name<'bump>]) -> Option<&'bump [Tactic<'bump>]> {
        self.try_parse(Token::KwBy, |s| s.parse_tactics(env))
    }

    // ── Func ──

    fn parse_func_expr(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        if !self.try_expect(&Token::KwFunc) {
            return Err(ParseError {
                message: "not a func expression".into(),
                span: 0..0,
            });
        }
        let name = self.parse_ident()?;
        let func_def = self.parse_func_body(name, env)?;
        Ok(self.arena.desugar_func_def(func_def))
    }

    // ── Dependent arrow ──

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
        Ok(self.arena.pi(x, a, self.parse_expr(&[x])?))
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
            Err(_) => {
                // `:` type-annotation suffix — suppressed in `#check`
                // context so that `:` is reserved for the constraint
                // separator (e.g. `#check s some_sth : str`).
                if !self.no_annot
                    && let Some(c) = self.try_parse(Token::Colon, |s| s.parse_expr(env))
                {
                    return self.parse_suffixes(env, self.arena.annot(t, c));
                }
                // `by` suffix: term by tactic1; tactic2; ...
                if !self.no_by
                    && let Some(tactics) = self.parse_by_proof_clause(env)
                {
                    return self.parse_suffixes(env, self.arena.by_proof(Some(t), tactics));
                }
                // `.field` suffix: dotted name access (struct construction/projection)
                if self.peek_token() == Some(Token::Dot) {
                    if let Term::Builtin(name) = t {
                        self.advance(); // consume `.`
                        let field = self.parse_ident()?;
                        let dotted = self.pool.intern(&format!("{}.{}", name, field));
                        return self.parse_suffixes(env, self.arena.builtin(dotted));
                    }
                }
                Ok(t)
            }
        }
    }

    // ── Atom ──

    fn builtin_atom(&mut self, name: &str) -> &'bump Term<'bump> {
        self.advance();
        self.arena.builtin(self.pool.intern(name))
    }

    fn parse_atom(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
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
            Some(Token::AndIntro) => Ok(self.builtin_atom("∧-intro")),
            Some(Token::AndElimLeft) => Ok(self.builtin_atom("∧-elim-left")),
            Some(Token::And) => Ok(self.builtin_atom("and")),
            Some(Token::Or) => Ok(self.builtin_atom("or")),
            Some(Token::Not) => Ok(self.builtin_atom("not")),
            Some(Token::Implies) => Ok(self.builtin_atom("implies")),
            Some(Token::KwAuto) => {
                self.advance();
                Ok(self.arena.auto_proof())
            }
            Some(Token::Ident(_)) => self.parse_var(env),
            Some(Token::Backslash) | Some(Token::Lambda) => self.parse_lam(env),
            Some(Token::Minus) => {
                self.advance();
                let t = self.parse_atom(env)?;
                Ok(self.arena.app(
                    self.arena
                        .app(self.arena.prim_op(PrimOp::Sub), self.arena.lit_int(0)),
                    t,
                ))
            }
            Some(Token::LParen) => self.parse_parens(env),
            Some(Token::KwBy) => {
                if self.no_by {
                    // Inside a type annotation, `by` belongs to the
                    // outer context (e.g., a let-binding proof clause).
                    return Err(ParseError {
                        message: "not a standalone by block".into(),
                        span: 0..0,
                    });
                }
                // Standalone `by` block (first-class proof).
                self.advance();
                let tactics = self.parse_tactics(env)?;
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

    fn parse_var(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        let name = self.parse_ident()?;
        if let Some(i) = env.iter().position(|n| *n == name) {
            Ok(self.arena.var(i))
        } else if KEYWORDS.contains(&name) {
            Err(ParseError {
                message: format!("keyword '{}' cannot be used as identifier", name),
                span: self.current_span(),
            })
        } else {
            Ok(self.arena.builtin(name))
        }
    }

    fn parse_ident(&mut self) -> Result<Name<'bump>, ParseError> {
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
        Ok(self.arena.lam(self.parse_expr(&extended_env)?))
    }

    fn parse_parens(&mut self, env: &[Name<'bump>]) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::LParen)?;
        // Inside parentheses, restore full annotation support even when
        // the outer context (e.g. `#check`) suppresses `:` annotations.
        let saved = self.no_annot;
        self.no_annot = false;
        let t = self.parse_expr(env)?;
        self.no_annot = saved;
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
        Ok(self.arena.refine(
            self.pool.intern(""),
            parent,
            replace_var_zero(self.arena, predicate),
        ))
    }

    // ── Operators ──

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
            if tok == Token::ThinArrow {
                self.advance();
                let rhs_atom = self.parse_app_any(env, no_annot)?;
                return Ok(self.arena.pi(
                    self.pool.intern(""),
                    lhs,
                    self.parse_binop_rhs(env, rhs_atom, next_min, no_annot)?,
                ));
            }
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
            lhs = self
                .arena
                .app(self.arena.app(self.arena.prim_op(op), lhs), rhs);
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

    // ── Tactic parsing ──

    /// Parse a sequence of tactics from a `by` block (Lean 4 style).
    /// Tactics are separated by newlines or semicolons.  The last tactic
    /// may be a bare expression (implicit `exact`).  Stops at terminator
    /// tokens (`:=`, `in`, `:`, `)`, etc.) or EOF.
    fn parse_tactics(&mut self, env: &[Name<'bump>]) -> Result<&'bump [Tactic<'bump>], ParseError> {
        let mut tactics: Vec<Tactic<'bump>> = Vec::new();
        loop {
            // Stop at tokens that end the tactic block.
            // We peek *before* advance skips newlines, so we also see
            // newlines as implicit separators — the next non-newline
            // token being a terminator ends the block.
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
                | Some((Token::HashShow, _)) => break,
                _ => {}
            }
            let tactic = self.parse_tactic(env)?;
            tactics.push(tactic);
            // Skip optional `;` separator.
            // Newlines are already consumed by `advance` inside
            // `parse_tactic`, so they act as implicit separators.
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

    /// Parse a single tactic: `exact <term>`, `apply <term>`, `intro [name]`,
    /// `have <name> := <term>`, or a bare expression (implicit `exact`).
    /// Uses `parse_term_no_annot` so that `:` and `by` are NOT consumed
    /// (they delimit the end of the tactic block).
    fn parse_tactic(&mut self, env: &[Name<'bump>]) -> Result<Tactic<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::KwExact) => {
                self.advance();
                let t = self.parse_app_no_annot(env)?;
                Ok(Tactic::Exact(t))
            }
            Some(Token::KwApply) => {
                self.advance();
                let t = self.parse_app_no_annot(env)?;
                Ok(Tactic::Apply(t))
            }
            Some(Token::KwIntro) => {
                self.advance();
                // Optional name: `intro x` or just `intro`
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
                let t = self.parse_app_no_annot(env)?;
                Ok(Tactic::Have(name, t))
            }
            // Bare expression = implicit `exact`
            _ => {
                let t = self.parse_app_no_annot(env)?;
                Ok(Tactic::Exact(t))
            }
        }
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
    arena.map(term, &|t| {
        if matches!(t, Term::Var(0)) {
            Some(arena.ref_param())
        } else {
            None
        }
    })
}

// ── Public entry points ──

fn tokenize(input: &str) -> Vec<SpannedToken> {
    Token::lexer(input)
        .spanned()
        .filter_map(|(r, s)| r.ok().map(|t| (t, s)))
        .collect()
}

pub fn parse_expr_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    let pool = StringPool::new(bump);
    Parser::new(&tokenize(input), &pool, arena)
        .parse_expr_top()
        .map_err(|e| e.to_string())
}

pub fn parse_def_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<(Name<'bump>, &'bump FuncDef<'bump>), String> {
    let pool = StringPool::new(bump);
    Parser::new(&tokenize(input), &pool, arena)
        .parse_def_top()
        .map_err(|e| e.to_string())
}

pub fn parse_program<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<Vec<TopLevel<'bump>>, String> {
    let pool = StringPool::new(bump);
    Parser::new(&tokenize(input), &pool, arena)
        .parse_program()
        .map_err(|e| e.to_string())
}
