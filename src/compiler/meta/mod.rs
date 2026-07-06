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

mod runtime;
mod splice;

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
            term = self.arena.app(term, self.meta_call_arg(arg, param_ty)?);
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
                                let proof = self.eval_tactic_call(name, args, goal)?;
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
