use super::*;

impl<'bump> Compiler<'bump> {
    pub(super) fn eval_tactic_call(
        &self,
        name: Name<'bump>,
        args: &'bump [&'bump Term<'bump>],
        goal: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let Some(entry) = self.tactics.get(name) else {
            return Err(Diagnostic::new(format!(
                "`{name}` is not a valid tactic (missing #[tactic] marker)"
            )));
        };
        let quoted_goal = self.quote_term(goal)?;
        let mut call = self.arena.named(entry.name);
        call = self.arena.app(call, quoted_goal);
        for (idx, arg) in args.iter().enumerate() {
            let param_ty = entry.params.get(idx + 1).and_then(|ty| *ty);
            call = self.arena.app(call, self.meta_call_arg(arg, param_ty)?);
        }
        let expanded = self.expand_meta(call)?;
        let resolved = self.try_resolve_meta_eval(expanded)?;
        let expr_constraint = self.arena.builtin(self.arena.alloc_str(EXPR_TYPE));
        self.checker
            .check(&empty_ctx(), resolved, expr_constraint)
            .map_err(|err| Diagnostic::new(format!("tactic `{name}` must return Expr: {err}")))?;
        let value = Evaluator::new(self.arena)
            .eval(resolved)
            .map_err(|err| Diagnostic::new(format!("tactic `{name}` eval failed: {err}")))?;
        self.decode_expr(value)
            .map_err(|err| Diagnostic::new(format!("tactic `{name}` produced invalid Expr: {err}")))
    }

    pub(super) fn meta_call_arg(
        &self,
        arg: &'bump Term<'bump>,
        param_ty: Option<&'bump Term<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        if param_ty.is_some_and(|ty| Compiler::is_meta_type_name(ty, EXPR_TYPE)) {
            self.quote_term(arg)
        } else {
            self.expand_meta(arg)
        }
    }

    pub(super) fn try_resolve_meta_eval(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let mut current = term;
        for _ in 0..=self.env.len() {
            current = self.try_resolve_all(current)?;
            if !self.contains_resolvable_global(current) {
                return Ok(current);
            }
        }
        Ok(current)
    }

    fn contains_resolvable_global(&self, term: &'bump Term<'bump>) -> bool {
        match term {
            Term::Builtin(name) | Term::Global(name) => self.env.contains_key(name),
            Term::App(f, a) => {
                self.contains_resolvable_global(f) || self.contains_resolvable_global(a)
            }
            Term::Implicit(inner)
            | Term::Lam(inner)
            | Term::NamedLam(_, inner)
            | Term::Unsafe(inner)
            | Term::Pure(inner)
            | Term::Quote(inner)
            | Term::Splice(inner)
            | Term::StructProj(inner, _) => self.contains_resolvable_global(inner),
            Term::Pi(_, a, b) | Term::Refine(_, a, b) => {
                self.contains_resolvable_global(a) || self.contains_resolvable_global(b)
            }
            // Meta eval only needs value-level globals to keep reducing; repeatedly
            // expanding annotation constraints can blow up on recursive meta types
            // like `Expr` and `Definitions`.
            Term::Annot(inner, _) => self.contains_resolvable_global(inner),
            Term::Let(_, value, body, constraint) => {
                self.contains_resolvable_global(value)
                    || self.contains_resolvable_global(body)
                    || constraint.is_some_and(|c| self.contains_resolvable_global(c))
            }
            Term::IfThenElse(c, t, e) => {
                self.contains_resolvable_global(c)
                    || self.contains_resolvable_global(t)
                    || self.contains_resolvable_global(e)
            }
            Term::ByProof(inner, tactics) => {
                inner.is_some_and(|t| self.contains_resolvable_global(t))
                    || tactics.iter().any(|tactic| match tactic {
                        Tactic::Exact(t) | Tactic::Apply(t) | Tactic::Have(_, t) => {
                            self.contains_resolvable_global(t)
                        }
                        Tactic::Intro(_) => false,
                        Tactic::Custom(_, args) => {
                            args.iter().any(|arg| self.contains_resolvable_global(arg))
                        }
                    })
            }
            Term::EnumDef(_, variants) => variants.iter().any(|(_, fields)| {
                fields
                    .iter()
                    .any(|(_, constraint)| self.contains_resolvable_global(constraint))
            }),
            Term::Variant(_, _, payloads) | Term::StructCons(_, payloads) => payloads
                .iter()
                .any(|payload| self.contains_resolvable_global(payload)),
            Term::NamedStructCons(_, fields) => fields
                .iter()
                .any(|(_, value)| self.contains_resolvable_global(value)),
            Term::Match(scrut, branches) => {
                self.contains_resolvable_global(scrut)
                    || branches.iter().any(|(_, binds, body)| {
                        binds
                            .iter()
                            .any(|(_, ty)| self.contains_resolvable_global(ty))
                            || self.contains_resolvable_global(body)
                    })
            }
            Term::NamedMatch(scrut, branches) => {
                self.contains_resolvable_global(scrut)
                    || branches.iter().any(|(_, binds, body)| {
                        binds
                            .iter()
                            .any(|(_, ty)| self.contains_resolvable_global(ty))
                            || self.contains_resolvable_global(body)
                    })
            }
            Term::Do(stmts) => stmts.iter().any(|stmt| match stmt {
                DoStmt::Bind(_, rhs) | DoStmt::Expr(rhs) => self.contains_resolvable_global(rhs),
                DoStmt::Let(_, rhs, constraint) => {
                    self.contains_resolvable_global(rhs)
                        || constraint.is_some_and(|c| self.contains_resolvable_global(c))
                }
            }),
            Term::StructDef(_, fields) => fields
                .iter()
                .any(|(_, constraint)| self.contains_resolvable_global(constraint)),
            Term::MethodCall(receiver, _) => self.contains_resolvable_global(receiver),
            Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::Named(_)
            | Term::AutoProof
            | Term::RefParam => false,
        }
    }

    pub(super) fn eval_splice(
        &self,
        inner: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let expanded = self.expand_meta(inner)?;
        let resolved = self.try_resolve_meta_eval(expanded)?;
        let expr_constraint = self.arena.builtin(self.arena.alloc_str(EXPR_TYPE));
        self.checker
            .check(&empty_ctx(), resolved, expr_constraint)
            .map_err(|err| {
                Diagnostic::new(format!("splice expression must have type Expr: {err}"))
            })?;
        let value = Evaluator::new(self.arena)
            .eval(resolved)
            .map_err(|err| Diagnostic::new(format!("splice eval failed: {err}")))?;
        self.decode_expr(value)
            .map_err(|err| Diagnostic::new(format!("splice produced invalid Expr: {err}")))
    }

    pub(super) fn quote_term(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        match term {
            Term::Splice(inner) => {
                let spliced = self.eval_splice(inner)?;
                self.quote_term(spliced)
            }
            Term::Quote(inner) => {
                let quoted = self.quote_term(inner)?;
                self.quote_term(quoted)
            }
            Term::LitInt(n) => Ok(self.expr_variant(EXPR_INT, &[self.arena.lit_int(*n)])),
            Term::LitBool(b) => Ok(self.expr_variant(EXPR_BOOL, &[self.arena.lit_bool(*b)])),
            Term::LitStr(s) => Ok(self.expr_variant(EXPR_STR, &[self.arena.lit_str(s)])),
            Term::Var(i) => Ok(self.expr_variant(EXPR_VAR, &[self.arena.lit_int(*i as i64)])),
            Term::Named(name) | Term::Builtin(name) => {
                Ok(self.expr_variant(EXPR_NAME, &[self.arena.lit_str(name)]))
            }
            Term::Global(name) => Ok(self.expr_variant(EXPR_GLOBAL, &[self.arena.lit_str(name)])),
            Term::PrimOp(op) => {
                let op = self.arena.alloc_str(&op.to_string());
                Ok(self.expr_variant(EXPR_PRIM, &[self.arena.lit_str(op)]))
            }
            Term::App(f, a) => {
                let f = self.quote_term(f)?;
                let a = self.quote_term(a)?;
                Ok(self.expr_variant(EXPR_APP, &[f, a]))
            }
            Term::NamedLam(_, body) | Term::Lam(body) => {
                let body = self.quote_term(body)?;
                Ok(self.expr_variant(EXPR_LAM, &[body]))
            }
            Term::Pi(name, domain, codomain) => {
                let domain = self.quote_term(domain)?;
                let codomain = self.quote_term(codomain)?;
                Ok(self.expr_variant(EXPR_PI, &[self.arena.lit_str(name), domain, codomain]))
            }
            Term::Let(name, value, body, _) => {
                let value = self.quote_term(value)?;
                let body = self.quote_term(body)?;
                Ok(self.expr_variant(EXPR_LET, &[self.arena.lit_str(name), value, body]))
            }
            Term::IfThenElse(c, t, e) => {
                let c = self.quote_term(c)?;
                let t = self.quote_term(t)?;
                let e = self.quote_term(e)?;
                Ok(self.expr_variant(EXPR_IF, &[c, t, e]))
            }
            Term::Annot(inner, constraint) => {
                let inner = self.quote_term(inner)?;
                let constraint = self.quote_term(constraint)?;
                Ok(self.expr_variant(EXPR_ANNOT, &[inner, constraint]))
            }
            Term::StructDef(name, _) => {
                Ok(self.expr_variant(EXPR_STRUCT_DEF, &[self.arena.lit_str(name)]))
            }
            Term::EnumDef(name, _) => {
                Ok(self.expr_variant(EXPR_ENUM_DEF, &[self.arena.lit_str(name)]))
            }
            other => Err(Diagnostic::new(format!(
                "quote does not support this term yet: {:?}",
                other
            ))),
        }
    }

    pub(super) fn expr_variant(
        &self,
        idx: usize,
        payloads: &[&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        self.arena.variant(
            self.arena.alloc_str(EXPR_TYPE),
            idx,
            self.arena.alloc_slice(payloads),
        )
    }

    pub(super) fn decode_expr(
        &self,
        expr: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        let expr = self.peel(expr);
        let Term::Variant(name, idx, payloads) = expr else {
            return Err(format!("expected Expr variant, got {:?}", expr));
        };
        if *name != EXPR_TYPE {
            return Err(format!("expected Expr, got {name}"));
        }
        match *idx {
            EXPR_INT => Ok(self.arena.lit_int(self.payload_int(payloads, 0)?)),
            EXPR_BOOL => Ok(self.arena.lit_bool(self.payload_bool(payloads, 0)?)),
            EXPR_STR => Ok(self.arena.lit_str(self.payload_str(payloads, 0)?)),
            EXPR_VAR => {
                let index = self.payload_int(payloads, 0)?;
                if index < 0 {
                    return Err("Var index must be non-negative".into());
                }
                Ok(self.arena.var(index as usize))
            }
            EXPR_NAME => {
                let name = self.payload_str(payloads, 0)?;
                if Self::is_builtin_term_name(name) {
                    Ok(self.arena.builtin(name))
                } else {
                    Ok(self.arena.named(name))
                }
            }
            EXPR_GLOBAL => Ok(self.arena.global(self.payload_str(payloads, 0)?)),
            EXPR_PRIM => {
                let op = self.payload_str(payloads, 0)?;
                let op = match op {
                    "+" => PrimOp::Add,
                    "-" => PrimOp::Sub,
                    "*" => PrimOp::Mul,
                    "/" => PrimOp::Div,
                    "%" => PrimOp::Mod_,
                    "==" => PrimOp::Eq,
                    "<" => PrimOp::Lt,
                    ">" => PrimOp::Gt,
                    "<=" => PrimOp::Le,
                    ">=" => PrimOp::Ge,
                    "/=" => PrimOp::Neq,
                    _ => return Err(format!("unknown primitive op `{op}`")),
                };
                Ok(self.arena.prim_op(op))
            }
            EXPR_APP => Ok(self.arena.app(
                self.decode_expr(self.payload(payloads, 0)?)?,
                self.decode_expr(self.payload(payloads, 1)?)?,
            )),
            EXPR_LAM => Ok(self
                .arena
                .lam(self.decode_expr(self.payload(payloads, 0)?)?)),
            EXPR_PI => Ok(self.arena.pi(
                self.payload_str(payloads, 0)?,
                self.decode_expr(self.payload(payloads, 1)?)?,
                self.decode_expr(self.payload(payloads, 2)?)?,
            )),
            EXPR_LET => Ok(self.arena.let_(
                self.payload_str(payloads, 0)?,
                self.decode_expr(self.payload(payloads, 1)?)?,
                self.decode_expr(self.payload(payloads, 2)?)?,
                None,
            )),
            EXPR_IF => Ok(self.arena.if_then_else(
                self.decode_expr(self.payload(payloads, 0)?)?,
                self.decode_expr(self.payload(payloads, 1)?)?,
                self.decode_expr(self.payload(payloads, 2)?)?,
            )),
            EXPR_ANNOT => Ok(self.arena.annot(
                self.decode_expr(self.payload(payloads, 0)?)?,
                self.decode_expr(self.payload(payloads, 1)?)?,
            )),
            EXPR_DEF | EXPR_INSTANCE => Err(format!(
                "Expr variant index {idx} is a top-level definition, not an expression"
            )),
            EXPR_STRUCT_DEF | EXPR_ENUM_DEF => Err(format!(
                "Expr variant index {idx} cannot be spliced as an expression"
            )),
            _ => Err(format!("unknown Expr variant index {idx}")),
        }
    }

    fn is_builtin_term_name(name: &str) -> bool {
        matches!(
            name,
            BUILTIN_INT
                | BUILTIN_I8
                | BUILTIN_I16
                | BUILTIN_I32
                | BUILTIN_I64
                | BUILTIN_U8
                | BUILTIN_U16
                | BUILTIN_U32
                | BUILTIN_U64
                | BUILTIN_C_INT
                | BUILTIN_C_UINT
                | BUILTIN_PTR
                | BUILTIN_PTR_CAST
                | BUILTIN_BOOL
                | BUILTIN_STR
                | BUILTIN_IO
                | BUILTIN_UNIT
                | BUILTIN_DATA
                | BUILTIN_PROP
                | BUILTIN_THEOREM
                | BUILTIN_PROOF
        )
    }

    pub(super) fn peel(&self, mut term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        while let Term::Annot(inner, _) | Term::Unsafe(inner) | Term::Pure(inner) = term {
            term = inner;
        }
        term
    }

    pub(super) fn payload(
        &self,
        payloads: &'bump [&'bump Term<'bump>],
        idx: usize,
    ) -> Result<&'bump Term<'bump>, String> {
        payloads
            .get(idx)
            .copied()
            .map(|term| self.peel(term))
            .ok_or_else(|| format!("missing payload {idx}"))
    }

    fn payload_int(
        &self,
        payloads: &'bump [&'bump Term<'bump>],
        idx: usize,
    ) -> Result<i64, String> {
        match self.payload(payloads, idx)? {
            Term::LitInt(n) => Ok(*n),
            other => Err(format!("expected int payload, got {:?}", other)),
        }
    }

    fn payload_bool(
        &self,
        payloads: &'bump [&'bump Term<'bump>],
        idx: usize,
    ) -> Result<bool, String> {
        match self.payload(payloads, idx)? {
            Term::LitBool(b) => Ok(*b),
            other => Err(format!("expected bool payload, got {:?}", other)),
        }
    }

    pub(super) fn payload_str(
        &self,
        payloads: &'bump [&'bump Term<'bump>],
        idx: usize,
    ) -> Result<Name<'bump>, String> {
        match self.payload(payloads, idx)? {
            Term::LitStr(s) => Ok(*s),
            other => Err(format!("expected string payload, got {:?}", other)),
        }
    }
}
