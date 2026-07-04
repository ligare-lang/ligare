use crate::checker::context::empty_ctx;
use crate::config::{
    BUILTIN_BOOL, BUILTIN_C_INT, BUILTIN_C_UINT, BUILTIN_DATA, BUILTIN_I8, BUILTIN_I16,
    BUILTIN_I32, BUILTIN_I64, BUILTIN_INT, BUILTIN_IO, BUILTIN_PROOF, BUILTIN_PROP, BUILTIN_PTR,
    BUILTIN_PTR_CAST, BUILTIN_STR, BUILTIN_THEOREM, BUILTIN_U8, BUILTIN_U16, BUILTIN_U32,
    BUILTIN_U64, BUILTIN_UNIT, COMPILER_BUILTIN_ATTRIBUTE_ATTR, COMPILER_INTRINSIC_ATTR,
    CUSTOM_ATTRIBUTE_ATTR, GLOBAL_ALLOCATOR_ATTR, TACTIC_ATTR, TERMINATING_ATTR,
};
use crate::core::eval::Evaluator;
use crate::core::syntax::{DoStmt, Name, PrimOp, Tactic, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::{Attribute, TopLevel};

use super::Compiler;

pub(crate) const EXPR_TYPE: &str = "Expr";
pub(crate) const DEFINITIONS_TYPE: &str = "Definitions";

const EXPR_INT: usize = 0;
const EXPR_BOOL: usize = 1;
const EXPR_STR: usize = 2;
const EXPR_VAR: usize = 3;
const EXPR_NAME: usize = 4;
const EXPR_GLOBAL: usize = 5;
const EXPR_PRIM: usize = 6;
const EXPR_APP: usize = 7;
const EXPR_LAM: usize = 8;
const EXPR_LET: usize = 9;
const EXPR_IF: usize = 10;
const EXPR_ANNOT: usize = 11;
const EXPR_DEF: usize = 12;
const EXPR_INSTANCE: usize = 13;
const EXPR_STRUCT_DEF: usize = 14;
const EXPR_ENUM_DEF: usize = 15;
const EXPR_PI: usize = 16;

const DEFINITIONS_NIL: usize = 0;
const DEFINITIONS_CONS: usize = 1;

impl<'bump> Compiler<'bump> {
    pub(crate) fn register_builtin_meta(&mut self) {
        if self.checker.lookup_enum(EXPR_TYPE).is_some()
            && self.checker.lookup_enum(DEFINITIONS_TYPE).is_some()
        {
            return;
        }
        let expr = self.arena.alloc_str(EXPR_TYPE);
        let definitions = self.arena.alloc_str(DEFINITIONS_TYPE);
        let int = self.arena.builtin(self.arena.alloc_str("int"));
        let bool_ = self.arena.builtin(self.arena.alloc_str("bool"));
        let str_ = self.arena.builtin(self.arena.alloc_str("str"));
        let expr_ty = self.arena.builtin(expr);
        let definitions_ty = self.arena.builtin(definitions);
        let variants: Vec<(&'bump str, &'bump [(&'bump str, &'bump Term<'bump>)])> = vec![
            ("Int", self.fields(&[("value", int)])),
            ("Bool", self.fields(&[("value", bool_)])),
            ("Str", self.fields(&[("value", str_)])),
            ("Var", self.fields(&[("index", int)])),
            ("Name", self.fields(&[("name", str_)])),
            ("Global", self.fields(&[("name", str_)])),
            ("Prim", self.fields(&[("op", str_)])),
            ("App", self.fields(&[("fun", expr_ty), ("arg", expr_ty)])),
            ("Lam", self.fields(&[("body", expr_ty)])),
            (
                "Let",
                self.fields(&[("name", str_), ("value", expr_ty), ("body", expr_ty)]),
            ),
            (
                "If",
                self.fields(&[
                    ("cond", expr_ty),
                    ("then_branch", expr_ty),
                    ("else_branch", expr_ty),
                ]),
            ),
            (
                "Annot",
                self.fields(&[("term", expr_ty), ("constraint", expr_ty)]),
            ),
            (
                "Def",
                self.fields(&[("name", str_), ("constraint", expr_ty), ("body", expr_ty)]),
            ),
            (
                "Instance",
                self.fields(&[("name", str_), ("constraint", expr_ty), ("value", expr_ty)]),
            ),
            ("StructDef", self.fields(&[("name", str_)])),
            ("EnumDef", self.fields(&[("name", str_)])),
            (
                "Pi",
                self.fields(&[("name", str_), ("domain", expr_ty), ("codomain", expr_ty)]),
            ),
        ];
        let def = self.arena.enum_def(expr, self.arena.alloc_slice(&variants));
        self.checker.add_enum(expr, def, &[]);
        self.env.insert(
            expr,
            self.arena
                .annot(def, self.arena.builtin(self.arena.alloc_str("prop"))),
        );

        let definitions_variants: Vec<(&'bump str, &'bump [(&'bump str, &'bump Term<'bump>)])> = vec![
            ("Nil", self.fields(&[])),
            (
                "Cons",
                self.fields(&[("head", expr_ty), ("tail", definitions_ty)]),
            ),
        ];
        let definitions_def = self
            .arena
            .enum_def(definitions, self.arena.alloc_slice(&definitions_variants));
        self.checker.add_enum(definitions, definitions_def, &[]);
        self.env.insert(
            definitions,
            self.arena.annot(
                definitions_def,
                self.arena.builtin(self.arena.alloc_str("prop")),
            ),
        );
    }

    fn fields(
        &self,
        fields: &[(&'bump str, &'bump Term<'bump>)],
    ) -> &'bump [(&'bump str, &'bump Term<'bump>)] {
        self.arena.alloc_slice(fields)
    }

    pub(crate) fn expand_meta_tops(
        &self,
        top: TopLevel<'bump>,
    ) -> Result<Vec<TopLevel<'bump>>, Diagnostic> {
        match top {
            TopLevel::TLAttributed(attrs, inner, span) => {
                let compiler_attrs = attrs
                    .iter()
                    .copied()
                    .filter(Self::is_compiler_attribute)
                    .collect::<Vec<_>>();
                let meta_attrs = attrs
                    .iter()
                    .copied()
                    .filter(|attr| !Self::is_compiler_attribute(attr))
                    .collect::<Vec<_>>();

                let mut out = Vec::new();
                let quoted_target = self.quote_top_level(inner)?;
                let inner = if compiler_attrs.is_empty() {
                    (*inner).clone()
                } else {
                    TopLevel::TLAttributed(
                        self.arena.alloc_slice(&compiler_attrs),
                        inner,
                        span.clone(),
                    )
                };
                out.push(self.expand_meta_top_single(inner)?);
                for attr in meta_attrs {
                    let splices = if attr.is_name("derive") {
                        self.derive_attribute_splice_terms(attr, quoted_target)?
                    } else {
                        vec![self.attribute_splice_term(attr, quoted_target)?]
                    };
                    for splice in splices {
                        out.extend(self.eval_definitions_splice(
                            splice,
                            span.clone(),
                            &format!("attribute `{}`", self.attribute_name(attr)),
                        )?);
                    }
                }
                Ok(out)
            }
            TopLevel::TLSplice(inner, span) => {
                self.eval_definitions_splice(inner, span, "top-level splice")
            }
            TopLevel::TLNamespace(name, items, span) => {
                let mut expanded_items = Vec::new();
                for item in items {
                    expanded_items.extend(self.expand_meta_tops(item.clone())?);
                }
                Ok(vec![TopLevel::TLNamespace(
                    name,
                    self.arena.bump().alloc_slice_clone(&expanded_items),
                    span,
                )])
            }
            other => Ok(vec![self.expand_meta_top_single(other)?]),
        }
    }

    fn expand_meta_top_single(&self, top: TopLevel<'bump>) -> Result<TopLevel<'bump>, Diagnostic> {
        Ok(match top {
            TopLevel::TLDef(name, params, ret, body, span) => {
                let params = self.expand_meta_params(params)?;
                let ret = ret.map(|t| self.expand_meta(t)).transpose()?;
                TopLevel::TLDef(
                    name,
                    params,
                    ret,
                    self.expand_meta_with_goal(body, ret)?,
                    span,
                )
            }
            TopLevel::TLExternDef(name, params, ret, span) => {
                let params = self.expand_meta_params(params)?;
                TopLevel::TLExternDef(name, params, self.expand_meta(ret)?, span)
            }
            TopLevel::TLInstance(name, constraint, value, span) => TopLevel::TLInstance(
                name,
                self.expand_meta(constraint)?,
                self.expand_meta(value)?,
                span,
            ),
            TopLevel::TLVariable(params, span) => {
                TopLevel::TLVariable(self.expand_meta_params(params)?, span)
            }
            TopLevel::TLCheck(term, constraint, span) => {
                TopLevel::TLCheck(self.expand_meta(term)?, self.expand_meta(constraint)?, span)
            }
            TopLevel::TLTheorem(name, prop, body, span) => {
                let prop = self.expand_meta(prop)?;
                TopLevel::TLTheorem(
                    name,
                    prop,
                    self.expand_meta_with_goal(body, Some(prop))?,
                    span,
                )
            }
            TopLevel::TLEval(term, span) => TopLevel::TLEval(self.expand_meta(term)?, span),
            TopLevel::TLExpr(term, span) => TopLevel::TLExpr(self.expand_meta(term)?, span),
            TopLevel::TLSplice(inner, span) => TopLevel::TLSplice(self.expand_meta(inner)?, span),
            TopLevel::TLPublic(inner) => TopLevel::TLPublic(
                self.arena
                    .bump()
                    .alloc(self.expand_meta_top_single((*inner).clone())?),
            ),
            TopLevel::TLAttributed(attrs, inner, span) => TopLevel::TLAttributed(
                attrs,
                self.arena
                    .bump()
                    .alloc(self.expand_meta_top_single((*inner).clone())?),
                span,
            ),
            TopLevel::TLNamespace(name, items, span) => {
                let items = items
                    .iter()
                    .cloned()
                    .map(|item| self.expand_meta_top_single(item))
                    .collect::<Result<Vec<_>, _>>()?;
                TopLevel::TLNamespace(name, self.arena.bump().alloc_slice_clone(&items), span)
            }
            other => other,
        })
    }

    fn is_compiler_attribute(attr: &Attribute<'_>) -> bool {
        attr.is_name(COMPILER_INTRINSIC_ATTR)
            || attr.is_name(COMPILER_BUILTIN_ATTRIBUTE_ATTR)
            || attr.is_name(GLOBAL_ALLOCATOR_ATTR)
            || attr.is_name(TERMINATING_ATTR)
            || attr.is_name(TACTIC_ATTR)
            || attr.is_name(CUSTOM_ATTRIBUTE_ATTR)
    }

    fn attribute_name(&self, attr: Attribute<'bump>) -> String {
        attr.path.join("::")
    }

    fn attribute_splice_term(
        &self,
        attr: Attribute<'bump>,
        quoted_target: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        if attr.is_name("derive") {
            return Err(Diagnostic::new(
                "`derive` must be expanded through derive_attribute_splices",
            ));
        }
        let attr_name = self.attribute_name(attr);
        let Some(entry) = self.attributes.get(attr_name.as_str()) else {
            return Err(Diagnostic::new(format!(
                "`{attr_name}` is not a valid attribute (missing #[attr] marker)"
            )));
        };
        let mut term = self.arena.named(entry.name);
        term = self.arena.app(term, quoted_target);
        for (idx, arg) in attr.args.iter().enumerate() {
            let param_ty = entry.params.get(idx + 1).and_then(|ty| *ty);
            term = self.arena.app(term, self.meta_call_arg(*arg, param_ty)?);
        }
        Ok(term)
    }

    fn derive_attribute_splice_terms(
        &self,
        attr: Attribute<'bump>,
        quoted_target: &'bump Term<'bump>,
    ) -> Result<Vec<&'bump Term<'bump>>, Diagnostic> {
        attr.args
            .iter()
            .map(|trait_arg| {
                let trait_name = self.derive_trait_name(trait_arg)?;
                let derive_name = if let Some((prefix, leaf)) = trait_name.rsplit_once("::") {
                    format!("{prefix}::derive_{leaf}")
                } else {
                    format!("derive_{trait_name}")
                };
                Ok(self.arena.app(
                    self.arena.named(self.arena.alloc_str(&derive_name)),
                    quoted_target,
                ))
            })
            .collect()
    }

    fn derive_trait_name(&self, term: &'bump Term<'bump>) -> Result<&'bump str, Diagnostic> {
        match term {
            Term::Named(name) | Term::Builtin(name) | Term::Global(name) => Ok(name),
            other => Err(Diagnostic::new(format!(
                "derive expects trait names, got {other:?}"
            ))),
        }
    }

    fn quote_top_level(&self, top: &TopLevel<'bump>) -> Result<&'bump Term<'bump>, Diagnostic> {
        match top {
            TopLevel::TLDef(name, _params, ret, body, _) => {
                let constraint =
                    ret.unwrap_or_else(|| self.arena.builtin(self.arena.alloc_str("data")));
                Ok(self.expr_variant(
                    EXPR_DEF,
                    &[
                        self.arena.lit_str(name),
                        self.quote_term(constraint)?,
                        self.quote_term(body)?,
                    ],
                ))
            }
            TopLevel::TLInstance(name, constraint, value, _) => Ok(self.expr_variant(
                EXPR_INSTANCE,
                &[
                    self.arena.lit_str(name),
                    self.quote_term(constraint)?,
                    self.quote_term(value)?,
                ],
            )),
            TopLevel::TLPublic(inner) | TopLevel::TLAttributed(_, inner, _) => {
                self.quote_top_level(inner)
            }
            other => Err(Diagnostic::new(format!(
                "attributes cannot quote this top-level item yet: {other:?}"
            ))),
        }
    }

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

    fn expand_meta_params(
        &self,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
    ) -> Result<&'bump [(Name<'bump>, Option<&'bump Term<'bump>>)], Diagnostic> {
        let params = params
            .iter()
            .map(|(name, constraint)| {
                Ok((*name, constraint.map(|c| self.expand_meta(c)).transpose()?))
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        Ok(self.arena.alloc_slice(&params))
    }

    pub(crate) fn expand_meta(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        self.expand_meta_with_goal(term, None)
    }

    fn expand_meta_with_goal(
        &self,
        term: &'bump Term<'bump>,
        goal: Option<&'bump Term<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        match term {
            Term::Quote(inner) => self.quote_term(inner),
            Term::Splice(inner) => self.eval_splice(inner),
            Term::App(f, a) => Ok(self.arena.app(self.expand_meta(f)?, self.expand_meta(a)?)),
            Term::Implicit(inner) => Ok(self.arena.implicit(self.expand_meta(inner)?)),
            Term::NamedLam(name, body) => Ok(self.arena.named_lam(name, self.expand_meta(body)?)),
            Term::Lam(body) => Ok(self.arena.lam(self.expand_meta(body)?)),
            Term::Pi(name, a, b) => {
                Ok(self
                    .arena
                    .pi(name, self.expand_meta(a)?, self.expand_meta(b)?))
            }
            Term::Let(name, value, body, constraint) => {
                let constraint = constraint.map(|c| self.expand_meta(c)).transpose()?;
                Ok(self.arena.let_(
                    name,
                    self.expand_meta_with_goal(value, constraint)?,
                    self.expand_meta(body)?,
                    constraint,
                ))
            }
            Term::IfThenElse(c, t, e) => Ok(self.arena.if_then_else(
                self.expand_meta(c)?,
                self.expand_meta(t)?,
                self.expand_meta(e)?,
            )),
            Term::Refine(name, parent, pred) => {
                Ok(self
                    .arena
                    .refine(name, self.expand_meta(parent)?, self.expand_meta(pred)?))
            }
            Term::Annot(inner, constraint) => {
                let constraint = self.expand_meta(constraint)?;
                Ok(self.arena.annot(
                    self.expand_meta_with_goal(inner, Some(constraint))?,
                    constraint,
                ))
            }
            Term::ByProof(inner, tactics) => {
                let inner = inner.map(|t| self.expand_meta(t)).transpose()?;
                let tactics = tactics
                    .iter()
                    .map(|tactic| {
                        Ok(match tactic {
                            Tactic::Exact(t) => Tactic::Exact(self.expand_meta(t)?),
                            Tactic::Apply(t) => Tactic::Apply(self.expand_meta(t)?),
                            Tactic::Intro(name) => Tactic::Intro(*name),
                            Tactic::Have(name, t) => Tactic::Have(name, self.expand_meta(t)?),
                            Tactic::Custom(name, args) => {
                                let goal = goal.ok_or_else(|| {
                                    Diagnostic::new(format!(
                                        "custom tactic `{name}` requires a known goal"
                                    ))
                                })?;
                                let proof = self.eval_tactic_call(*name, args, goal)?;
                                Tactic::Exact(proof)
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.by_proof(inner, self.arena.alloc_slice(&tactics)))
            }
            Term::EnumDef(name, variants) => {
                let variants = variants
                    .iter()
                    .map(|(variant, fields)| {
                        let fields = fields
                            .iter()
                            .map(|(field, constraint)| Ok((*field, self.expand_meta(constraint)?)))
                            .collect::<Result<Vec<_>, Diagnostic>>()?;
                        Ok((*variant, self.arena.alloc_slice(&fields)))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.enum_def(name, self.arena.alloc_slice(&variants)))
            }
            Term::Variant(name, idx, payloads) => {
                let payloads = payloads
                    .iter()
                    .map(|payload| self.expand_meta(payload))
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .variant(name, *idx, self.arena.alloc_slice(&payloads)))
            }
            Term::Match(scrut, branches) => {
                let branches = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let binds = binds
                            .iter()
                            .map(|(name, constraint)| Ok((*name, self.expand_meta(constraint)?)))
                            .collect::<Result<Vec<_>, Diagnostic>>()?;
                        Ok((
                            *idx,
                            self.arena.alloc_slice(&binds),
                            self.expand_meta(body)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .match_(self.expand_meta(scrut)?, self.arena.alloc_slice(&branches)))
            }
            Term::NamedMatch(scrut, branches) => {
                let branches = branches
                    .iter()
                    .map(|(variant, binds, body)| {
                        let binds = binds
                            .iter()
                            .map(|(name, constraint)| Ok((*name, self.expand_meta(constraint)?)))
                            .collect::<Result<Vec<_>, Diagnostic>>()?;
                        Ok((
                            *variant,
                            self.arena.alloc_slice(&binds),
                            self.expand_meta(body)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .named_match(self.expand_meta(scrut)?, self.arena.alloc_slice(&branches)))
            }
            Term::Do(stmts) => {
                let stmts = stmts
                    .iter()
                    .map(|stmt| match stmt {
                        DoStmt::Bind(name, rhs) => Ok(DoStmt::Bind(name, self.expand_meta(rhs)?)),
                        DoStmt::Let(name, rhs, constraint) => Ok(DoStmt::Let(
                            name,
                            self.expand_meta(rhs)?,
                            constraint.map(|c| self.expand_meta(c)).transpose()?,
                        )),
                        DoStmt::Expr(expr) => Ok(DoStmt::Expr(self.expand_meta(expr)?)),
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.do_(self.arena.alloc_slice(&stmts)))
            }
            Term::Unsafe(inner) => Ok(self.arena.unsafe_(self.expand_meta(inner)?)),
            Term::Pure(inner) => Ok(self.arena.pure(self.expand_meta(inner)?)),
            Term::StructDef(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field, constraint)| Ok((*field, self.expand_meta(constraint)?)))
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.struct_def(name, self.arena.alloc_slice(&fields)))
            }
            Term::StructCons(name, values) => {
                let values = values
                    .iter()
                    .map(|value| self.expand_meta(value))
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .struct_cons(name, self.arena.alloc_slice(&values)))
            }
            Term::StructProj(subject, idx) => {
                Ok(self.arena.struct_proj(self.expand_meta(subject)?, *idx))
            }
            Term::MethodCall(receiver, method) => {
                Ok(self.arena.method_call(self.expand_meta(receiver)?, method))
            }
            _ => Ok(term),
        }
    }

    fn eval_tactic_call(
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
            call = self.arena.app(call, self.meta_call_arg(*arg, param_ty)?);
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

    fn meta_call_arg(
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

    fn try_resolve_meta_eval(
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
            Term::Pi(_, a, b) | Term::Annot(a, b) | Term::Refine(_, a, b) => {
                self.contains_resolvable_global(a) || self.contains_resolvable_global(b)
            }
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

    fn eval_splice(&self, inner: &'bump Term<'bump>) -> Result<&'bump Term<'bump>, Diagnostic> {
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

    fn quote_term(&self, term: &'bump Term<'bump>) -> Result<&'bump Term<'bump>, Diagnostic> {
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

    fn expr_variant(&self, idx: usize, payloads: &[&'bump Term<'bump>]) -> &'bump Term<'bump> {
        self.arena.variant(
            self.arena.alloc_str(EXPR_TYPE),
            idx,
            self.arena.alloc_slice(payloads),
        )
    }

    fn decode_expr(&self, expr: &'bump Term<'bump>) -> Result<&'bump Term<'bump>, String> {
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

    fn peel(&self, mut term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        while let Term::Annot(inner, _) | Term::Unsafe(inner) | Term::Pure(inner) = term {
            term = inner;
        }
        term
    }

    fn payload(
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

    fn payload_str(
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::pool::TermArena;
    use crate::front::parser::parse_expr_top;
    use bumpalo::Bump;

    #[test]
    fn quote_builds_expected_expr_ast() {
        let bump = Bump::new();
        let arena = TermArena::new(&bump);
        let compiler = Compiler::new(&bump, &arena);
        let term = parse_expr_top("quote { 1 + 2 }", &bump, &arena).unwrap();
        let quoted = compiler.expand_meta(term).unwrap();
        let Term::Variant("Expr", EXPR_APP, app_payloads) = quoted else {
            panic!("expected Expr.App, got {quoted:?}");
        };
        assert_eq!(app_payloads.len(), 2);
        let Term::Variant("Expr", EXPR_APP, op_payloads) = app_payloads[0] else {
            panic!("expected nested Expr.App, got {:?}", app_payloads[0]);
        };
        let Term::Variant("Expr", EXPR_PRIM, prim_payloads) = op_payloads[0] else {
            panic!("expected Expr.Prim, got {:?}", op_payloads[0]);
        };
        assert!(matches!(prim_payloads[0], Term::LitStr("+")));
        assert!(matches!(op_payloads[1], Term::Variant("Expr", EXPR_INT, _)));
        assert!(matches!(
            app_payloads[1],
            Term::Variant("Expr", EXPR_INT, _)
        ));
    }
}
