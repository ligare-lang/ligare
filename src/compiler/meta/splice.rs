use super::*;

impl<'bump> Compiler<'bump> {
    pub(crate) fn eval_definitions_splice(
        &self,
        inner: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
        origin: &str,
    ) -> Result<Vec<TopLevel<'bump>>, Diagnostic> {
        let expanded = self.expand_meta(inner)?;
        let resolved = self.try_resolve_meta_eval(expanded)?;
        let definitions_constraint = self.arena.builtin(self.arena.alloc_str(DEFINITIONS_TYPE));
        self.checker
            .check(&empty_ctx(), resolved, definitions_constraint)
            .map_err(|err| {
                Diagnostic::with_span(
                    format!("{origin} must have type Definitions: {err}"),
                    span.clone(),
                )
            })?;
        let value = Evaluator::new(self.arena).eval(resolved).map_err(|err| {
            Diagnostic::with_span(format!("{origin} eval failed: {err}"), span.clone())
        })?;
        self.decode_definitions(value, span.clone()).map_err(|err| {
            Diagnostic::with_span(
                format!("{origin} produced invalid Definitions: {err}"),
                span,
            )
        })
    }

    fn decode_definitions(
        &self,
        value: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<Vec<TopLevel<'bump>>, String> {
        let mut out = Vec::new();
        let mut cursor = self.peel(value);
        loop {
            let Term::Variant(name, idx, payloads) = cursor else {
                return Err(format!("expected Definitions variant, got {cursor:?}"));
            };
            if *name != DEFINITIONS_TYPE {
                return Err(format!("expected Definitions, got {name}"));
            }
            match *idx {
                DEFINITIONS_NIL => return Ok(out),
                DEFINITIONS_CONS => {
                    let head = self.payload(payloads, 0)?;
                    out.push(self.decode_top_level_expr(head, span.clone())?);
                    cursor = self.payload(payloads, 1)?;
                }
                _ => return Err(format!("unknown Definitions variant index {idx}")),
            }
        }
    }

    fn decode_top_level_expr(
        &self,
        expr: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<TopLevel<'bump>, String> {
        let expr = self.peel(expr);
        let Term::Variant(name, idx, payloads) = expr else {
            return Err(format!("expected Expr top-level variant, got {expr:?}"));
        };
        if *name != EXPR_TYPE {
            return Err(format!("expected Expr, got {name}"));
        }
        match *idx {
            EXPR_DEF => Ok(TopLevel::TLDef(
                self.payload_str(payloads, 0)?,
                {
                    let constraint = self.decode_expr(self.payload(payloads, 1)?)?;
                    self.params_from_pi(constraint).0
                },
                {
                    let constraint = self.decode_expr(self.payload(payloads, 1)?)?;
                    Some(self.params_from_pi(constraint).1)
                },
                {
                    let constraint = self.decode_expr(self.payload(payloads, 1)?)?;
                    let param_count = self.params_from_pi(constraint).0.len();
                    self.strip_lams(self.decode_expr(self.payload(payloads, 2)?)?, param_count)
                },
                span,
            )),
            EXPR_INSTANCE => Ok(TopLevel::TLInstance(
                self.payload_str(payloads, 0)?,
                self.decode_expr(self.payload(payloads, 1)?)?,
                self.decode_expr(self.payload(payloads, 2)?)?,
                span,
            )),
            _ => Err(format!(
                "Expr variant index {idx} is not a top-level definition"
            )),
        }
    }

    fn params_from_pi(
        &self,
        constraint: &'bump Term<'bump>,
    ) -> (
        &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        &'bump Term<'bump>,
    ) {
        let mut params = Vec::new();
        let mut cursor = constraint;
        while let Term::Pi(name, domain, codomain) = cursor {
            params.push((*name, Some(*domain)));
            cursor = codomain;
        }
        (self.arena.alloc_slice(&params), cursor)
    }

    fn strip_lams(&self, mut body: &'bump Term<'bump>, mut count: usize) -> &'bump Term<'bump> {
        while count > 0 {
            if let Term::Lam(inner) | Term::NamedLam(_, inner) = body {
                body = inner;
            } else {
                break;
            }
            count -= 1;
        }
        body
    }
}
