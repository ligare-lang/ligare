//! Name resolution and substitution passes.
//!
//! Functions that walk the AST to resolve `Builtin`/`Named` references
//! to their definitions, convert variant/struct constructor applications,
//! and perform top-level substitution.

use crate::checker::context::Context;
use crate::config::BUILTIN_INT;
use crate::core::syntax::{DoStmt, Name, PrimOp, Tactic, Term};
use crate::diagnostic::Diagnostic;

/// Result of collecting variant constructor args: (enum_name, variant_index, field_specs, args).
pub type VariantWithArgs<'bump> = (
    Name<'bump>,
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    Vec<&'bump Term<'bump>>,
);

/// Result of collecting struct constructor args: (struct_name, field_specs, args).
pub type StructWithArgs<'bump> = (
    Name<'bump>,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    Vec<&'bump Term<'bump>>,
);

use super::Compiler;

#[derive(Clone, Copy)]
pub(crate) struct MethodScopeEntry<'bump> {
    pub name: Name<'bump>,
    pub constraint: Option<&'bump Term<'bump>>,
}

impl<'bump> Compiler<'bump> {
    /// Resolve ALL free `Builtin(name)`/`Named(name)` references from the env
    /// (constants AND functions). Used for eval paths where function bodies
    /// need to be available.
    ///
    /// Local binders must become de Bruijn indices before global substitution,
    /// otherwise a global definition named `x` could capture `fun x => ...`.
    pub fn resolve_all(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.try_resolve_all(term)
            .expect("resolve_all failed; use try_resolve_all for parser terms")
    }

    pub fn try_resolve_all(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        self.try_resolve_all_with_expected(term, None)
    }

    pub(crate) fn try_resolve_all_with_expected(
        &self,
        term: &'bump Term<'bump>,
        expected: Option<&'bump Term<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let term = self.rewrite_method_calls(term, &mut Vec::new())?;
        let term = self.checker.desugar_with_context(term)?;
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t
                && !crate::config::is_std_intrinsic_name(name)
                && let Some(def) = self.env.get(name)
            {
                return Some(def);
            }
            None
        });
        let t = self.elaborate_implicit_apps(t)?;
        // Also resolve variant apps, struct constructors, and zero-arg constructors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        let t = self.fold_struct_projections(t);
        let t = self.arena.map(t, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
                    && field_specs.is_empty()
                {
                    return Some(self.arena.variant(uname, idx, &[]));
                }
                // Zero-arg struct constructor
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
                    && fields.is_empty()
                {
                    return Some(self.arena.struct_cons(sname, &[]));
                }
                // Struct projector
                if let Some(_idx) = self.checker.lookup_struct_proj(name) {
                    // Can't resolve without subject — leave as-is
                }
            }
            None
        });
        let t = self.fold_struct_projections(t);
        self.elaborate_of_nat_literals(t, &Context::empty(), expected)
    }

    pub(crate) fn resolve_instance_value(
        &self,
        term: &'bump Term<'bump>,
        expected: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let term = self.rewrite_method_calls(term, &mut Vec::new())?;
        let term = self.checker.desugar_with_context(term)?;
        let term = self.elaborate_implicit_apps(term)?;
        let term = self.resolve_variant_apps(term);
        let term = self.resolve_struct_ctors(term);
        let term = self.resolve_struct_projs(term);
        let term = self.fold_struct_projections(term);
        self.elaborate_of_nat_literals(term, &Context::empty(), Some(expected))
    }

    pub(crate) fn rewrite_method_calls(
        &self,
        term: &'bump Term<'bump>,
        scope: &mut Vec<MethodScopeEntry<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        match term {
            Term::MethodCall(receiver, method) => {
                self.rewrite_method_call(receiver, method, &[], scope)
            }
            Term::App(f, a) => {
                if let Some((op, receiver, rhs)) = Self::operator_app_spine(term) {
                    let rhs = self.rewrite_method_calls(rhs, scope)?;
                    let method = self.primop_method_name(op);
                    match self.rewrite_interface_method_call(receiver, method, scope) {
                        Ok(call) => return Ok(self.arena.app(call, rhs)),
                        Err(err)
                            if err.message.starts_with(
                                "no interface instance or function provides method",
                            ) || err
                                .message
                                .starts_with("cannot infer receiver constraint for method") =>
                        {
                            return Ok(self.arena.app(
                                self.rewrite_method_calls(f, scope)?,
                                self.rewrite_method_calls(a, scope)?,
                            ));
                        }
                        Err(err) => return Err(err),
                    }
                }
                if let Some((receiver, method, args)) = Self::method_call_app_spine(term) {
                    let args = args
                        .iter()
                        .map(|arg| self.rewrite_method_calls(arg, scope))
                        .collect::<Result<Vec<_>, Diagnostic>>()?;
                    let call = self.rewrite_method_call(receiver, method, &args, scope)?;
                    return Ok(args.into_iter().fold(call, |f, arg| self.arena.app(f, arg)));
                }
                Ok(self.arena.app(
                    self.rewrite_method_calls(f, scope)?,
                    self.rewrite_method_calls(a, scope)?,
                ))
            }
            Term::Implicit(inner) => Ok(self
                .arena
                .implicit(self.rewrite_method_calls(inner, scope)?)),
            Term::NamedLam(name, body) => {
                scope.push(MethodScopeEntry {
                    name,
                    constraint: None,
                });
                let body = self.rewrite_method_calls(body, scope)?;
                scope.pop();
                Ok(self.arena.named_lam(name, body))
            }
            Term::Lam(body) => Ok(self.arena.lam(self.rewrite_method_calls(body, scope)?)),
            Term::Pi(name, a, b) => {
                let a = self.rewrite_method_calls(a, scope)?;
                scope.push(MethodScopeEntry {
                    name,
                    constraint: Some(a),
                });
                let b = self.rewrite_method_calls(b, scope)?;
                scope.pop();
                Ok(self.arena.pi(name, a, b))
            }
            Term::Let(name, value, body, constraint) => {
                let value = self.rewrite_method_calls(value, scope)?;
                let constraint = constraint
                    .map(|c| self.rewrite_method_calls(c, scope))
                    .transpose()?;
                let entry_idx = scope.len();
                scope.push(MethodScopeEntry {
                    name,
                    constraint: constraint
                        .or_else(|| self.infer_literal_or_value_constraint(value)),
                });
                let body = self.rewrite_method_calls(body, scope)?;
                let constraint = constraint.or_else(|| scope[entry_idx].constraint);
                scope.pop();
                Ok(self.arena.let_(name, value, body, constraint))
            }
            Term::IfThenElse(c, t, f) => Ok(self.arena.if_then_else(
                self.rewrite_method_calls(c, scope)?,
                self.rewrite_method_calls(t, scope)?,
                self.rewrite_method_calls(f, scope)?,
            )),
            Term::Refine(name, parent, pred) => {
                let parent = self.rewrite_method_calls(parent, scope)?;
                scope.push(MethodScopeEntry {
                    name,
                    constraint: Some(parent),
                });
                let pred = self.rewrite_method_calls(pred, scope)?;
                scope.pop();
                Ok(self.arena.refine(name, parent, pred))
            }
            Term::Annot(inner, constraint) => Ok(self.arena.annot(
                self.rewrite_method_calls(inner, scope)?,
                self.rewrite_method_calls(constraint, scope)?,
            )),
            Term::ByProof(inner, tactics) => {
                let inner = inner
                    .map(|t| self.rewrite_method_calls(t, scope))
                    .transpose()?;
                let tactics = tactics
                    .iter()
                    .map(|tactic| {
                        Ok(match tactic {
                            Tactic::Exact(t) => Tactic::Exact(self.rewrite_method_calls(t, scope)?),
                            Tactic::Apply(t) => Tactic::Apply(self.rewrite_method_calls(t, scope)?),
                            Tactic::Intro(n) => Tactic::Intro(*n),
                            Tactic::Have(n, t) => {
                                Tactic::Have(n, self.rewrite_method_calls(t, scope)?)
                            }
                            Tactic::Custom(n, args) => {
                                let args = args
                                    .iter()
                                    .map(|arg| self.rewrite_method_calls(arg, scope))
                                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                                Tactic::Custom(n, self.arena.alloc_slice(&args))
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
                            .map(|(field, constraint)| {
                                Ok((*field, self.rewrite_method_calls(constraint, scope)?))
                            })
                            .collect::<Result<Vec<_>, Diagnostic>>()?;
                        Ok((*variant, self.arena.alloc_slice(&fields)))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.enum_def(name, self.arena.alloc_slice(&variants)))
            }
            Term::StructDef(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field, constraint)| {
                        Ok((*field, self.rewrite_method_calls(constraint, scope)?))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.struct_def(name, self.arena.alloc_slice(&fields)))
            }
            Term::Variant(name, idx, payloads) => {
                let payloads = payloads
                    .iter()
                    .map(|payload| self.rewrite_method_calls(payload, scope))
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .variant(name, *idx, self.arena.alloc_slice(&payloads)))
            }
            Term::StructCons(name, values) => {
                let values = values
                    .iter()
                    .map(|value| self.rewrite_method_calls(value, scope))
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .struct_cons(name, self.arena.alloc_slice(&values)))
            }
            Term::NamedStructCons(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field, value)| Ok((*field, self.rewrite_method_calls(value, scope)?)))
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .named_struct_cons(*name, self.arena.alloc_slice(&fields)))
            }
            Term::StructProj(subject, idx) => Ok(self
                .arena
                .struct_proj(self.rewrite_method_calls(subject, scope)?, *idx)),
            Term::Match(scrut, branches) => {
                let scrut = self.rewrite_method_calls(scrut, scope)?;
                let branches = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        for (name, constraint) in binds.iter().rev() {
                            scope.push(MethodScopeEntry {
                                name,
                                constraint: Some(*constraint),
                            });
                        }
                        let body = self.rewrite_method_calls(body, scope)?;
                        for _ in *binds {
                            scope.pop();
                        }
                        Ok((*idx, *binds, body))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.match_(scrut, self.arena.alloc_slice(&branches)))
            }
            Term::NamedMatch(scrut, branches) => {
                let scrut = self.rewrite_method_calls(scrut, scope)?;
                let branches = branches
                    .iter()
                    .map(|(variant, binds, body)| {
                        for (name, constraint) in binds.iter().rev() {
                            scope.push(MethodScopeEntry {
                                name,
                                constraint: Some(*constraint),
                            });
                        }
                        let body = self.rewrite_method_calls(body, scope)?;
                        for _ in *binds {
                            scope.pop();
                        }
                        Ok((*variant, *binds, body))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .named_match(scrut, self.arena.alloc_slice(&branches)))
            }
            Term::Do(stmts) => {
                let mut stmts_out = Vec::with_capacity(stmts.len());
                let scope_len = scope.len();
                let mut pushed_let_stmt_indices = Vec::new();
                for stmt in stmts.iter() {
                    match stmt {
                        DoStmt::Bind(name, rhs) => {
                            let rhs = self.rewrite_method_calls(rhs, scope)?;
                            stmts_out.push(DoStmt::Bind(name, rhs));
                            scope.push(MethodScopeEntry {
                                name,
                                constraint: None,
                            });
                        }
                        DoStmt::Let(name, rhs, constraint) => {
                            let rhs = self.rewrite_method_calls(rhs, scope)?;
                            let constraint = constraint
                                .map(|c| self.rewrite_method_calls(c, scope))
                                .transpose()?;
                            stmts_out.push(DoStmt::Let(name, rhs, constraint));
                            pushed_let_stmt_indices.push((scope.len(), stmts_out.len() - 1));
                            scope.push(MethodScopeEntry {
                                name,
                                constraint: constraint
                                    .or_else(|| self.infer_literal_or_value_constraint(rhs)),
                            });
                        }
                        DoStmt::Expr(expr) => {
                            stmts_out.push(DoStmt::Expr(self.rewrite_method_calls(expr, scope)?));
                        }
                    }
                }
                for (scope_idx, stmt_idx) in pushed_let_stmt_indices {
                    let DoStmt::Let(name, rhs, constraint) = stmts_out[stmt_idx] else {
                        continue;
                    };
                    if constraint.is_none() {
                        stmts_out[stmt_idx] = DoStmt::Let(name, rhs, scope[scope_idx].constraint);
                    }
                }
                scope.truncate(scope_len);
                Ok(self.arena.do_(self.arena.alloc_slice(&stmts_out)))
            }
            Term::Unsafe(inner) => Ok(self.arena.unsafe_(self.rewrite_method_calls(inner, scope)?)),
            Term::Pure(inner) => Ok(self.arena.pure(self.rewrite_method_calls(inner, scope)?)),
            Term::Quote(inner) => Ok(self.arena.quote(inner)),
            Term::Splice(inner) => Ok(self.arena.splice(self.rewrite_method_calls(inner, scope)?)),
            _ => Ok(term),
        }
    }

    fn rewrite_method_call(
        &self,
        receiver: &'bump Term<'bump>,
        method: Name<'bump>,
        trailing_args: &[&'bump Term<'bump>],
        scope: &mut Vec<MethodScopeEntry<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let receiver = self.rewrite_method_calls(receiver, scope)?;
        let receiver_constraint = self.infer_parser_receiver_constraint(receiver, scope)?;
        if let Some(receiver_constraint) = receiver_constraint {
            let mut candidates = self
                .checker
                .lookup_method_instances(method, receiver_constraint);
            let env = self.method_scope_names(scope);
            for entry in scope.iter().rev() {
                let Some(constraint) = entry.constraint else {
                    continue;
                };
                let constraint = self.checker.desugar_with_names_context(constraint, &env)?;
                let value = self.arena.named(entry.name);
                if let Some(candidate) = self.checker.lookup_method_on_instance(
                    method,
                    receiver_constraint,
                    entry.name,
                    constraint,
                    value,
                ) {
                    candidates.push(candidate);
                }
            }
            if candidates.len() > 1 {
                let names = candidates
                    .iter()
                    .map(|candidate| candidate.name.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                return Err(Diagnostic::new(format!(
                    "ambiguous method `{method}` for receiver: {names}"
                )));
            }
            if let Some(candidate) = candidates.first().copied() {
                let projector = self.arena.named(
                    self.arena
                        .alloc_str(&format!("{}.{}", candidate.interface_name, method)),
                );
                return Ok(self
                    .arena
                    .app(self.arena.app(projector, candidate.value), receiver));
            }
        }

        if let Some((call, refined_receiver_constraint)) =
            self.rewrite_plain_function_method(receiver, method, receiver_constraint, trailing_args)
        {
            if let Some(constraint) = refined_receiver_constraint {
                self.refine_receiver_scope_constraint(receiver, constraint, scope);
            }
            return Ok(call);
        }

        match receiver_constraint {
            Some(_) => Err(Diagnostic::new(format!(
                "no interface instance or function provides method `{method}` for receiver"
            ))),
            None => Err(Diagnostic::new(format!(
                "cannot infer receiver constraint for method `{method}`"
            ))),
        }
    }

    fn rewrite_interface_method_call(
        &self,
        receiver: &'bump Term<'bump>,
        method: Name<'bump>,
        scope: &mut Vec<MethodScopeEntry<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let receiver = self.rewrite_method_calls(receiver, scope)?;
        let Some(receiver_constraint) = self.infer_parser_receiver_constraint(receiver, scope)?
        else {
            return Err(Diagnostic::new(format!(
                "cannot infer receiver constraint for method `{method}`"
            )));
        };

        let mut candidates = self
            .checker
            .lookup_method_instances(method, receiver_constraint);
        let env = self.method_scope_names(scope);
        for entry in scope.iter().rev() {
            let Some(constraint) = entry.constraint else {
                continue;
            };
            let constraint = self.checker.desugar_with_names_context(constraint, &env)?;
            let value = self.arena.named(entry.name);
            if let Some(candidate) = self.checker.lookup_method_on_instance(
                method,
                receiver_constraint,
                entry.name,
                constraint,
                value,
            ) {
                candidates.push(candidate);
            }
        }
        if candidates.len() > 1 {
            let names = candidates
                .iter()
                .map(|candidate| candidate.name.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Diagnostic::new(format!(
                "ambiguous method `{method}` for receiver: {names}"
            )));
        }
        let Some(candidate) = candidates.first().copied() else {
            return Err(Diagnostic::new(format!(
                "no interface instance or function provides method `{method}` for receiver"
            )));
        };
        let projector = self.arena.named(
            self.arena
                .alloc_str(&format!("{}.{}", candidate.interface_name, method)),
        );
        Ok(self
            .arena
            .app(self.arena.app(projector, candidate.value), receiver))
    }

    fn rewrite_plain_function_method(
        &self,
        receiver: &'bump Term<'bump>,
        method: Name<'bump>,
        receiver_constraint: Option<&'bump Term<'bump>>,
        trailing_args: &[&'bump Term<'bump>],
    ) -> Option<(&'bump Term<'bump>, Option<&'bump Term<'bump>>)> {
        let (function_name, receiver_type_args) =
            self.plain_method_function_name(method, receiver_constraint)?;
        let mut f = self.arena.named(self.arena.alloc_str(function_name));
        let implicit_args =
            self.plain_method_implicit_args(function_name, &receiver_type_args, trailing_args);
        for arg in &implicit_args {
            f = self.arena.app(f, arg);
        }
        let refined_receiver_constraint = self.refined_receiver_constraint(
            receiver_constraint,
            &receiver_type_args,
            &implicit_args,
        );
        Some((self.arena.app(f, receiver), refined_receiver_constraint))
    }

    fn plain_method_function_name(
        &self,
        method: Name<'bump>,
        receiver_constraint: Option<&'bump Term<'bump>>,
    ) -> Option<(&str, Vec<&'bump Term<'bump>>)> {
        if self.env.contains_key(method) {
            return Some((method, Vec::new()));
        }
        let (receiver_type, receiver_type_args) =
            receiver_constraint.and_then(|c| self.constraint_head_and_args(c))?;
        let method_leaf = method.rsplit("::").next().unwrap_or(method);
        let candidate = self
            .arena
            .alloc_str(&format!("{receiver_type}::{method_leaf}"));
        self.env
            .contains_key(candidate)
            .then_some((candidate, receiver_type_args))
    }

    fn plain_method_implicit_args(
        &self,
        function_name: &str,
        receiver_type_args: &[&'bump Term<'bump>],
        trailing_args: &[&'bump Term<'bump>],
    ) -> Vec<&'bump Term<'bump>> {
        let mut implicit_count = self.leading_meta_implicit_count(function_name);
        if implicit_count == 0 && receiver_type_args.is_empty() {
            implicit_count = self.namespace_type_param_count(function_name);
        }
        if implicit_count == 0 {
            return Vec::new();
        }
        let mut args = receiver_type_args
            .iter()
            .copied()
            .take(implicit_count)
            .collect::<Vec<_>>();
        for arg in trailing_args {
            if args.len() >= implicit_count {
                break;
            }
            if let Some(constraint) = self.infer_literal_or_value_constraint(arg) {
                args.push(constraint);
            }
        }
        args
    }

    fn namespace_type_param_count(&self, function_name: &str) -> usize {
        let Some((type_name, _)) = function_name.rsplit_once("::") else {
            return 0;
        };
        self.checker
            .lookup_enum(type_name)
            .map(|(_, params)| params.len())
            .or_else(|| {
                self.checker
                    .lookup_struct(type_name)
                    .map(|(_, params)| params.len())
            })
            .unwrap_or(0)
    }

    fn refined_receiver_constraint(
        &self,
        receiver_constraint: Option<&'bump Term<'bump>>,
        receiver_type_args: &[&'bump Term<'bump>],
        implicit_args: &[&'bump Term<'bump>],
    ) -> Option<&'bump Term<'bump>> {
        if !receiver_type_args.is_empty() || implicit_args.is_empty() {
            return None;
        }
        let (receiver_type, existing_args) =
            receiver_constraint.and_then(|c| self.constraint_head_and_args(c))?;
        if !existing_args.is_empty() {
            return None;
        }
        Some(self.apply_type_args(receiver_type, implicit_args))
    }

    fn apply_type_args(
        &self,
        type_name: Name<'bump>,
        type_args: &[&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        type_args
            .iter()
            .fold(self.arena.global(type_name), |f, arg| {
                self.arena.app(f, arg)
            })
    }

    fn refine_receiver_scope_constraint(
        &self,
        receiver: &'bump Term<'bump>,
        refined: &'bump Term<'bump>,
        scope: &mut [MethodScopeEntry<'bump>],
    ) {
        let Term::Named(name) = receiver else {
            return;
        };
        let Some(entry) = scope.iter_mut().rev().find(|entry| entry.name == *name) else {
            return;
        };
        let Some(current) = entry.constraint else {
            entry.constraint = Some(refined);
            return;
        };
        let Some((current_head, current_args)) = self.constraint_head_and_args(current) else {
            return;
        };
        let Some((refined_head, refined_args)) = self.constraint_head_and_args(refined) else {
            return;
        };
        if current_head == refined_head && current_args.is_empty() && !refined_args.is_empty() {
            entry.constraint = Some(refined);
        }
    }

    fn leading_meta_implicit_count(&self, function_name: &str) -> usize {
        let Some(term) = self.env.get(function_name).copied() else {
            return 0;
        };
        let Term::Annot(_, mut signature) = *term else {
            return 0;
        };
        let mut count = 0;
        while let Ok(Term::Pi(_, domain, codomain)) = self.checker.evaluator.whnf(signature) {
            let is_leading_type_param =
                if crate::checker::TypeChecker::is_implicit_constraint(domain) {
                    self.is_implicit_meta_constraint(domain)
                } else {
                    crate::core::semantics::SemanticQueries::new(self.checker.builtins())
                        .is_erased_parameter_constraint(domain)
                };
            if !is_leading_type_param {
                break;
            }
            count += 1;
            signature = codomain;
        }
        count
    }

    fn constraint_head_and_args(
        &self,
        constraint: &'bump Term<'bump>,
    ) -> Option<(&'bump str, Vec<&'bump Term<'bump>>)> {
        let mut head = constraint;
        let mut args = Vec::new();
        while let Term::App(f, a) = head {
            args.push(*a);
            head = f;
        }
        args.reverse();
        match head {
            Term::Builtin(name)
            | Term::Global(name)
            | Term::Named(name)
            | Term::EnumDef(name, _)
            | Term::StructDef(name, _) => Some((*name, args)),
            _ => None,
        }
    }

    fn method_call_app_spine(
        term: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, Name<'bump>, Vec<&'bump Term<'bump>>)> {
        let mut head = term;
        let mut args = Vec::new();
        while let Term::App(f, a) = head {
            args.push(*a);
            head = f;
        }
        args.reverse();
        if let Term::MethodCall(receiver, method) = head {
            Some((*receiver, *method, args))
        } else {
            None
        }
    }

    fn operator_app_spine(
        term: &'bump Term<'bump>,
    ) -> Option<(PrimOp, &'bump Term<'bump>, &'bump Term<'bump>)> {
        let Term::App(f, rhs) = term else {
            return None;
        };
        let Term::App(head, lhs) = f else {
            return None;
        };
        let Term::PrimOp(op) = head else {
            return None;
        };
        Some((*op, *lhs, *rhs))
    }

    fn primop_method_name(&self, op: PrimOp) -> Name<'bump> {
        self.arena.alloc_str(match op {
            PrimOp::Add => "add",
            PrimOp::Sub => "sub",
            PrimOp::Mul => "mul",
            PrimOp::Div => "div",
            PrimOp::Mod_ => "mod_",
            PrimOp::Eq => "eq",
            PrimOp::Lt => "lt",
            PrimOp::Gt => "gt",
            PrimOp::Le => "le",
            PrimOp::Ge => "ge",
            PrimOp::Neq => "neq",
        })
    }

    fn infer_parser_receiver_constraint(
        &self,
        term: &'bump Term<'bump>,
        scope: &[MethodScopeEntry<'bump>],
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        if let Some(constraint) = self.infer_literal_or_value_constraint(term) {
            return Ok(Some(constraint));
        }
        match term {
            Term::Named(name) => {
                let env = self.method_scope_names(scope);
                for entry in scope.iter().rev() {
                    if entry.name == *name {
                        return entry
                            .constraint
                            .map(|constraint| {
                                self.checker.desugar_with_names_context(constraint, &env)
                            })
                            .transpose();
                    }
                }
                Ok(self.env.get(name).and_then(|def| {
                    if let Term::Annot(_, constraint) = def {
                        Some(*constraint)
                    } else {
                        None
                    }
                }))
            }
            Term::Annot(_, constraint) => Ok(Some(self.checker.desugar_with_context(constraint)?)),
            _ => Ok(None),
        }
    }

    fn infer_literal_or_value_constraint(
        &self,
        term: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        match term {
            Term::LitInt(_) => Some(self.arena.builtin(self.arena.alloc_str("int"))),
            Term::LitBool(_) => Some(self.arena.builtin(self.arena.alloc_str("bool"))),
            Term::LitStr(_) => Some(self.arena.builtin(self.arena.alloc_str("str"))),
            Term::StructCons(name, _) | Term::Variant(name, _, _) => Some(self.arena.builtin(name)),
            Term::Annot(_, constraint) => Some(*constraint),
            Term::Named(name) | Term::Builtin(name) | Term::Global(name) => self
                .checker
                .lookup_variant(name)
                .and_then(|(enum_name, _, fields)| {
                    fields.is_empty().then(|| self.arena.builtin(enum_name))
                }),
            _ => None,
        }
    }

    fn method_scope_names(&self, scope: &[MethodScopeEntry<'bump>]) -> Vec<&'bump str> {
        scope.iter().rev().map(|entry| entry.name).collect()
    }

    /// Extract the function name from a term if it's a recursive call.
    /// Only returns `Some(name)` if the head is a `Builtin(name)` that
    /// maps to a function (i.e., has `Lam` body) in the env.
    pub fn extract_func_name(&self, term: &'bump Term<'bump>) -> Option<Name<'bump>> {
        let mut head = term;
        while let Term::App(f, _) = head {
            head = f;
        }
        if let Term::Builtin(name) | Term::Global(name) = head
            && let Some(def) = self.env.get(name)
        {
            if def.is_constant() {
                return None; // constants don't need self-reference
            }
            return Some(name);
        }
        None
    }

    /// Substitute known top-level definitions into a term (O(1) lookup).
    /// Also resolves variant/struct constructors to their term forms.
    /// Uses `is_constant()` to distinguish constants from functions.
    pub fn subst_top_level(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // First pass: resolve env lookups for constants only
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t
                && !crate::config::is_std_intrinsic_name(name)
                && let Some(def) = self.env.get(name)
                && def.is_constant()
            {
                return Some(def);
            }
            None
        });
        let t = self.elaborate_implicit_apps(t).unwrap_or(t);
        // Second pass: resolve variant apps, struct constructors, and projectors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        let t = self.fold_struct_projections(t);
        // Third pass: resolve remaining zero-arg variant/struct constructors
        let t = self.arena.map(t, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
                    && field_specs.is_empty()
                {
                    return Some(self.arena.variant(uname, idx, &[]));
                }
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
                    && fields.is_empty()
                {
                    return Some(self.arena.struct_cons(sname, &[]));
                }
            }
            None
        });
        self.fold_struct_projections(t)
    }

    fn elaborate_implicit_apps(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        match term {
            Term::App(f, a) => {
                let f = self.elaborate_implicit_apps(f)?;
                let a = self.elaborate_implicit_apps(a)?;
                let f = self.apply_pending_implicits_for_arg(f, a)?;
                Ok(self.arena.app(f, a))
            }
            Term::Let(n, v, b, mc) => {
                let v = self.elaborate_implicit_apps(v)?;
                let b = self.elaborate_implicit_apps(b)?;
                let mc = mc.map(|c| self.elaborate_implicit_apps(c)).transpose()?;
                Ok(self.arena.let_(n, v, b, mc))
            }
            Term::Lam(body) => Ok(self.arena.lam(self.elaborate_implicit_apps(body)?)),
            Term::Pi(n, a, b) => Ok(self.arena.pi(
                n,
                self.elaborate_implicit_apps(a)?,
                self.elaborate_implicit_apps(b)?,
            )),
            Term::IfThenElse(c, t, e) => Ok(self.arena.if_then_else(
                self.elaborate_implicit_apps(c)?,
                self.elaborate_implicit_apps(t)?,
                self.elaborate_implicit_apps(e)?,
            )),
            Term::Annot(inner, c) => Ok(self.arena.annot(
                self.elaborate_implicit_apps(inner)?,
                self.elaborate_implicit_apps(c)?,
            )),
            Term::Unsafe(inner) => Ok(self.arena.unsafe_(self.elaborate_implicit_apps(inner)?)),
            Term::Pure(inner) => Ok(self.arena.pure(self.elaborate_implicit_apps(inner)?)),
            Term::StructCons(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|f| self.elaborate_implicit_apps(f))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self
                    .arena
                    .struct_cons(name, self.arena.alloc_slice(&fields)))
            }
            Term::StructProj(subject, idx) => Ok(self
                .arena
                .struct_proj(self.elaborate_implicit_apps(subject)?, *idx)),
            Term::Variant(name, idx, payloads) => {
                let payloads = payloads
                    .iter()
                    .map(|p| self.elaborate_implicit_apps(p))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self
                    .arena
                    .variant(name, *idx, self.arena.alloc_slice(&payloads)))
            }
            Term::Match(scrut, branches) => {
                let scrut = self.elaborate_implicit_apps(scrut)?;
                let branches = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        Ok((*idx, *binds, self.elaborate_implicit_apps(body)?))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.match_(scrut, self.arena.alloc_slice(&branches)))
            }
            Term::Quote(inner) => Ok(self.arena.quote(inner)),
            Term::Splice(inner) => Ok(self.arena.splice(self.elaborate_implicit_apps(inner)?)),
            _ => Ok(term),
        }
    }

    fn apply_pending_implicits_for_arg(
        &self,
        mut f: &'bump Term<'bump>,
        explicit_arg: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        while let Some(domain) = self.leading_implicit_domain(f)? {
            if self.is_implicit_meta_constraint(domain) {
                if self.is_explicit_constraint_arg(explicit_arg) {
                    break;
                }
                if let Some(inferred) = self.infer_elab_constraint(explicit_arg) {
                    f = self.arena.app(f, inferred);
                    continue;
                }
            }
            let Some((_, instance)) = self.checker.lookup_instance(domain)? else {
                return Err(Diagnostic::new(format!(
                    "missing implicit instance for {}",
                    crate::pretty::PrettyPrinter::pretty(
                        crate::checker::TypeChecker::implicit_inner(domain)
                    )
                )));
            };
            f = self.arena.app(f, instance);
        }
        Ok(f)
    }

    fn is_explicit_constraint_arg(&self, term: &'bump Term<'bump>) -> bool {
        matches!(
            term,
            Term::Builtin(_)
                | Term::Global(_)
                | Term::Universe(_)
                | Term::EnumDef(..)
                | Term::StructDef(..)
        ) || matches!(term, Term::App(head, _) if self.is_explicit_constraint_arg(head))
    }

    fn leading_implicit_domain(
        &self,
        f: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        let Some(sig) = self.infer_app_signature(f)? else {
            return Ok(None);
        };
        let sig = self.checker.evaluator.whnf(sig)?;
        if let Term::Pi(_, domain, _) = sig
            && crate::checker::TypeChecker::is_implicit_constraint(domain)
        {
            return Ok(Some(domain));
        }
        Ok(None)
    }

    fn infer_app_signature(
        &self,
        f: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        match f {
            Term::Annot(_, sig) => Ok(Some(sig)),
            Term::Builtin(name) | Term::Global(name) => Ok(self.env.get(name).and_then(|def| {
                if let Term::Annot(_, sig) = def {
                    Some(*sig)
                } else {
                    None
                }
            })),
            Term::App(inner, arg) => {
                let Some(sig) = self.infer_app_signature(inner)? else {
                    return Ok(None);
                };
                let sig = self.checker.evaluator.whnf(sig)?;
                if let Term::Pi(_, _, codomain) = sig {
                    let sub = crate::core::debruijn::SubstitutionContext::new(self.arena);
                    Ok(Some(sub.instantiate_pi(arg, codomain)))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    fn is_implicit_meta_constraint(&self, term: &'bump Term<'bump>) -> bool {
        let Ok(inner) = self
            .checker
            .evaluator
            .whnf(crate::checker::TypeChecker::implicit_inner(term))
        else {
            return false;
        };
        matches!(
            inner,
            Term::Builtin(name) | Term::Global(name)
                if matches!(
                    crate::config::canonical_builtin_name(name),
                    "prop" | "theorem" | "proof" | "data"
                )
        ) || matches!(
            inner,
            Term::Universe(
                crate::core::syntax::Universe::UProp
                    | crate::core::syntax::Universe::UTheorem
                    | crate::core::syntax::Universe::UProof
                    | crate::core::syntax::Universe::UData
            )
        )
    }

    fn infer_elab_constraint(&self, term: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        match term {
            Term::Annot(_, constraint) => Some(constraint),
            Term::LitInt(_) => Some(self.arena.builtin(self.arena.alloc_str("int"))),
            Term::LitBool(_) => Some(self.arena.builtin(self.arena.alloc_str("bool"))),
            Term::LitStr(_) => Some(self.arena.builtin(self.arena.alloc_str("str"))),
            Term::StructCons(name, _) | Term::Variant(name, _, _) => Some(self.arena.builtin(name)),
            Term::Builtin(name) | Term::Global(name) => self.env.get(name).and_then(|def| {
                if let Term::Annot(_, constraint) = def {
                    Some(*constraint)
                } else {
                    None
                }
            }),
            _ => None,
        }
    }

    pub(crate) fn elaborate_of_nat_literals(
        &self,
        term: &'bump Term<'bump>,
        ctx: &Context<'bump>,
        expected: Option<&'bump Term<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        match term {
            Term::LitInt(n) => {
                if let Some(expected) = expected
                    && let Some(lowered) = self.lower_of_nat_literal(*n, expected)?
                {
                    return Ok(lowered);
                }
                Ok(term)
            }
            Term::App(f, a) => {
                let f = self.elaborate_of_nat_literals(f, ctx, None)?;
                let arg_expected = self.explicit_app_domain(ctx, f);
                let a = self.elaborate_of_nat_literals(a, ctx, arg_expected)?;
                Ok(self.arena.app(f, a))
            }
            Term::Annot(inner, constraint) => {
                let constraint = self.elaborate_of_nat_literals(constraint, ctx, None)?;
                let inner = self.elaborate_of_nat_literals(inner, ctx, Some(constraint))?;
                Ok(self.arena.annot(inner, constraint))
            }
            Term::Lam(body) => {
                let (next_ctx, body_expected) = if let Some(expected) = expected {
                    match self.checker.evaluator.whnf(expected)? {
                        Term::Pi(_, domain, codomain) => (ctx.extend_term(domain), Some(*codomain)),
                        _ => (ctx.clone(), None),
                    }
                } else {
                    (ctx.clone(), None)
                };
                Ok(self.arena.lam(self.elaborate_of_nat_literals(
                    body,
                    &next_ctx,
                    body_expected,
                )?))
            }
            Term::Pi(name, domain, codomain) => {
                let domain = self.elaborate_of_nat_literals(domain, ctx, None)?;
                let next_ctx = ctx.extend(name, domain);
                let codomain = self.elaborate_of_nat_literals(codomain, &next_ctx, None)?;
                Ok(self.arena.pi(name, domain, codomain))
            }
            Term::Let(name, value, body, constraint) => {
                let constraint = constraint
                    .map(|c| self.elaborate_of_nat_literals(c, ctx, None))
                    .transpose()?;
                let value = self.elaborate_of_nat_literals(value, ctx, constraint)?;
                let binding_constraint =
                    constraint.or_else(|| self.checker.infer_binding_constraint(ctx, value).ok());
                let next_ctx = binding_constraint
                    .map(|c| ctx.extend(name, c))
                    .unwrap_or_else(|| ctx.clone());
                let body = self.elaborate_of_nat_literals(body, &next_ctx, expected)?;
                Ok(self.arena.let_(name, value, body, constraint))
            }
            Term::IfThenElse(cond, then_branch, else_branch) => Ok(self.arena.if_then_else(
                self.elaborate_of_nat_literals(cond, ctx, None)?,
                self.elaborate_of_nat_literals(then_branch, ctx, expected)?,
                self.elaborate_of_nat_literals(else_branch, ctx, expected)?,
            )),
            Term::ByProof(inner, tactics) => {
                let inner = inner
                    .map(|t| self.elaborate_of_nat_literals(t, ctx, expected))
                    .transpose()?;
                let tactics = tactics
                    .iter()
                    .map(|tactic| {
                        Ok(match tactic {
                            Tactic::Exact(t) => {
                                Tactic::Exact(self.elaborate_of_nat_literals(t, ctx, None)?)
                            }
                            Tactic::Apply(t) => {
                                Tactic::Apply(self.elaborate_of_nat_literals(t, ctx, None)?)
                            }
                            Tactic::Intro(n) => Tactic::Intro(*n),
                            Tactic::Have(n, t) => {
                                Tactic::Have(n, self.elaborate_of_nat_literals(t, ctx, None)?)
                            }
                            Tactic::Custom(n, args) => {
                                let args = args
                                    .iter()
                                    .map(|arg| self.elaborate_of_nat_literals(arg, ctx, None))
                                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                                Tactic::Custom(n, self.arena.alloc_slice(&args))
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.by_proof(inner, self.arena.alloc_slice(&tactics)))
            }
            Term::Refine(name, parent, predicate) => {
                let parent = self.elaborate_of_nat_literals(parent, ctx, None)?;
                let predicate =
                    self.elaborate_of_nat_literals(predicate, &ctx.extend(name, parent), None)?;
                Ok(self.arena.refine(name, parent, predicate))
            }
            Term::StructCons(name, fields) => {
                let field_constraints =
                    self.checker
                        .lookup_struct(name)
                        .and_then(|(def, _)| match def {
                            Term::StructDef(_, fields) => Some(*fields),
                            _ => None,
                        });
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(idx, field)| {
                        let expected = field_constraints.and_then(|constraints| {
                            constraints.get(idx).map(|(_, constraint)| *constraint)
                        });
                        self.elaborate_of_nat_literals(field, ctx, expected)
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .struct_cons(name, self.arena.alloc_slice(&fields)))
            }
            Term::NamedStructCons(name, fields) => {
                let (struct_name, type_args, struct_fields) =
                    self.resolve_named_struct_target(*name, expected)?;
                let values = self.elaborate_named_struct_fields(
                    struct_name,
                    struct_fields,
                    type_args.as_deref(),
                    fields,
                    ctx,
                )?;
                Ok(self
                    .arena
                    .struct_cons(struct_name, self.arena.alloc_slice(&values)))
            }
            Term::Variant(name, idx, payloads) => {
                let payload_constraints =
                    self.checker
                        .lookup_enum(name)
                        .and_then(|(def, _)| match def {
                            Term::EnumDef(_, variants) => {
                                variants.get(*idx).map(|(_, fields)| *fields)
                            }
                            _ => None,
                        });
                let payloads = payloads
                    .iter()
                    .enumerate()
                    .map(|(payload_idx, payload)| {
                        let expected = payload_constraints.and_then(|fields| {
                            fields.get(payload_idx).map(|(_, constraint)| *constraint)
                        });
                        self.elaborate_of_nat_literals(payload, ctx, expected)
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .variant(name, *idx, self.arena.alloc_slice(&payloads)))
            }
            Term::Match(scrutinee, branches) => {
                let scrutinee = self.elaborate_of_nat_literals(scrutinee, ctx, None)?;
                let branches = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let mut branch_ctx = ctx.clone();
                        for (name, constraint) in binds.iter().rev() {
                            branch_ctx = branch_ctx.extend(name, constraint);
                        }
                        Ok((
                            *idx,
                            *binds,
                            self.elaborate_of_nat_literals(body, &branch_ctx, expected)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self
                    .arena
                    .match_(scrutinee, self.arena.alloc_slice(&branches)))
            }
            Term::StructProj(subject, idx) => Ok(self
                .arena
                .struct_proj(self.elaborate_of_nat_literals(subject, ctx, None)?, *idx)),
            Term::Unsafe(inner) => Ok(self
                .arena
                .unsafe_(self.elaborate_of_nat_literals(inner, ctx, expected)?)),
            Term::Pure(inner) => Ok(self
                .arena
                .pure(self.elaborate_of_nat_literals(inner, ctx, expected)?)),
            Term::Implicit(inner) => Ok(self
                .arena
                .implicit(self.elaborate_of_nat_literals(inner, ctx, None)?)),
            Term::EnumDef(name, variants) => {
                let variants = variants
                    .iter()
                    .map(|(variant, fields)| {
                        let fields = fields
                            .iter()
                            .map(|(field, constraint)| {
                                Ok((
                                    *field,
                                    self.elaborate_of_nat_literals(constraint, ctx, None)?,
                                ))
                            })
                            .collect::<Result<Vec<_>, Diagnostic>>()?;
                        Ok((*variant, self.arena.alloc_slice(&fields)))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.enum_def(name, self.arena.alloc_slice(&variants)))
            }
            Term::StructDef(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field, constraint)| {
                        Ok((
                            *field,
                            self.elaborate_of_nat_literals(constraint, ctx, None)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.struct_def(name, self.arena.alloc_slice(&fields)))
            }
            Term::Quote(_) | Term::Splice(_) | Term::AutoProof | Term::RefParam => Ok(term),
            _ => Ok(term),
        }
    }

    fn explicit_app_domain(
        &self,
        ctx: &Context<'bump>,
        f: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let constraint = self.checker.infer_binding_constraint(ctx, f).ok()?;
        match self.checker.evaluator.whnf(constraint).ok()? {
            Term::Pi(_, domain, _) => Some(domain),
            _ => None,
        }
    }

    fn resolve_named_struct_target(
        &self,
        explicit_name: Option<Name<'bump>>,
        expected: Option<&'bump Term<'bump>>,
    ) -> Result<
        (
            Name<'bump>,
            Option<Vec<&'bump Term<'bump>>>,
            &'bump [(Name<'bump>, &'bump Term<'bump>)],
        ),
        Diagnostic,
    > {
        if let Some(name) = explicit_name {
            let (def, _) = self
                .checker
                .lookup_struct(name)
                .ok_or_else(|| Diagnostic::new(format!("unknown struct in initializer: {name}")))?;
            let Term::StructDef(actual_name, fields) = def else {
                return Err(Diagnostic::new(format!(
                    "{name} is not a struct constraint"
                )));
            };
            let type_args = expected.and_then(|expected| {
                self.constraint_type_args_for(*actual_name, expected)
            });
            return Ok((*actual_name, type_args, *fields));
        }

        let Some(expected) = expected else {
            return Err(Diagnostic::new(
                "cannot infer struct type for initializer; add a constraint or use Type{...}"
                    .to_string(),
            ));
        };
        let Some((head, type_args)) = self.constraint_head_and_args(
            crate::checker::TypeChecker::implicit_inner(expected),
        ) else {
            return Err(Diagnostic::new(format!(
                "expected a struct constraint for initializer, got {}",
                crate::pretty::PrettyPrinter::pretty(expected)
            )));
        };
        let Some((def, _)) = self.checker.lookup_struct(head) else {
            return Err(Diagnostic::new(format!(
                "expected a struct constraint for initializer, got {}",
                crate::pretty::PrettyPrinter::pretty(expected)
            )));
        };
        let Term::StructDef(actual_name, fields) = def else {
            return Err(Diagnostic::new(format!(
                "expected a struct constraint for initializer, got {}",
                crate::pretty::PrettyPrinter::pretty(expected)
            )));
        };
        Ok((*actual_name, Some(type_args), *fields))
    }

    fn elaborate_named_struct_fields(
        &self,
        struct_name: Name<'bump>,
        struct_fields: &'bump [(Name<'bump>, &'bump Term<'bump>)],
        type_args: Option<&[&'bump Term<'bump>]>,
        named_fields: &'bump [(Name<'bump>, &'bump Term<'bump>)],
        ctx: &Context<'bump>,
    ) -> Result<Vec<&'bump Term<'bump>>, Diagnostic> {
        for (idx, (field_name, _)) in named_fields.iter().enumerate() {
            if named_fields[..idx]
                .iter()
                .any(|(seen_name, _)| seen_name == field_name)
            {
                return Err(Diagnostic::new(format!(
                    "struct {struct_name} initializer duplicates field `{field_name}`"
                )));
            }
            if !struct_fields.iter().any(|(name, _)| name == field_name) {
                return Err(Diagnostic::new(format!(
                    "struct {struct_name} has no field `{field_name}`"
                )));
            }
        }

        let mut ordered = Vec::with_capacity(struct_fields.len());
        for (field_name, field_constraint) in struct_fields.iter() {
            let Some((_, value)) = named_fields.iter().find(|(name, _)| name == field_name) else {
                return Err(Diagnostic::new(format!(
                    "struct {struct_name} initializer is missing field `{field_name}`"
                )));
            };
            let field_constraint = if let Some(type_args) = type_args {
                self.replace_generic_constraint_vars(*field_constraint, type_args)
            } else {
                *field_constraint
            };
            ordered.push(self.elaborate_of_nat_literals(
                value,
                ctx,
                Some(field_constraint),
            )?);
        }
        Ok(ordered)
    }

    fn constraint_type_args_for(
        &self,
        expected_name: Name<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Option<Vec<&'bump Term<'bump>>> {
        let mut args = Vec::new();
        let mut current = crate::checker::TypeChecker::implicit_inner(constraint);
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        match current {
            Term::Builtin(name) | Term::Global(name) if *name == expected_name => Some(args),
            _ => match self
                .checker
                .evaluator
                .whnf(crate::checker::TypeChecker::implicit_inner(constraint))
                .ok()?
            {
                Term::StructDef(name, _) if *name == expected_name => Some(args),
                _ => None,
            },
        }
    }

    fn replace_generic_constraint_vars(
        &self,
        term: &'bump Term<'bump>,
        type_args: &[&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        self.replace_generic_constraint_vars_at(term, type_args, 0)
    }

    fn replace_generic_constraint_vars_at(
        &self,
        term: &'bump Term<'bump>,
        type_args: &[&'bump Term<'bump>],
        depth: usize,
    ) -> &'bump Term<'bump> {
        match term {
            Term::Var(i) if *i >= depth && (*i - depth) < type_args.len() => {
                type_args[type_args.len() - 1 - (*i - depth)]
            }
            Term::App(f, a) => self.arena.app(
                self.replace_generic_constraint_vars_at(f, type_args, depth),
                self.replace_generic_constraint_vars_at(a, type_args, depth),
            ),
            Term::Implicit(inner) => self.arena.implicit(
                self.replace_generic_constraint_vars_at(inner, type_args, depth),
            ),
            Term::Pi(name, a, b) => self.arena.pi(
                name,
                self.replace_generic_constraint_vars_at(a, type_args, depth),
                self.replace_generic_constraint_vars_at(b, type_args, depth + 1),
            ),
            Term::Annot(inner, constraint) => self.arena.annot(
                self.replace_generic_constraint_vars_at(inner, type_args, depth),
                self.replace_generic_constraint_vars_at(constraint, type_args, depth),
            ),
            _ => term,
        }
    }

    fn lower_of_nat_literal(
        &self,
        value: i64,
        expected: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        let expected = self
            .checker
            .evaluator
            .whnf(crate::checker::TypeChecker::implicit_inner(expected))?;
        if self.constraint_accepts_raw_int(expected) {
            return Ok(None);
        }
        let Some(interface_name) = self.of_nat_interface_name() else {
            return Ok(None);
        };
        let wanted = self.arena.app(self.arena.global(interface_name), expected);
        let Some((_, instance)) = self.checker.lookup_instance(wanted)? else {
            return Ok(None);
        };
        let Some(field) = self.instance_field(instance, interface_name, "of_nat") else {
            return Ok(None);
        };
        Ok(Some(self.arena.app(field, self.arena.lit_int(value))))
    }

    fn constraint_accepts_raw_int(&self, expected: &'bump Term<'bump>) -> bool {
        let int = self.arena.builtin(self.arena.alloc_str("int"));
        matches!(expected, Term::Builtin(name) | Term::Global(name) if crate::config::is_builtin_name(name, BUILTIN_INT))
            || expected == int
            || self.checker.is_refinement_of(expected, int)
    }

    fn of_nat_interface_name(&self) -> Option<Name<'bump>> {
        self.checker
            .struct_table
            .iter()
            .find(|(name, _, _)| name.rsplit("::").next().unwrap_or(name) == "OfNat")
            .map(|(name, _, _)| *name)
    }

    fn instance_field(
        &self,
        instance: &'bump Term<'bump>,
        interface_name: Name<'bump>,
        field_name: &str,
    ) -> Option<&'bump Term<'bump>> {
        let proj_name = self
            .arena
            .alloc_str(&format!("{interface_name}.{field_name}"));
        let idx = self.checker.lookup_struct_proj(proj_name)?;
        let instance = match instance {
            Term::Annot(inner, _) => *inner,
            _ => instance,
        };
        match instance {
            Term::StructCons(_, values) => values.get(idx).copied(),
            _ => Some(self.arena.struct_proj(instance, idx)),
        }
    }

    pub(crate) fn fold_struct_projections(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::StructProj(subject, idx) = node
                && let Term::StructCons(_, values) = subject
                && values.iter().any(|value| Self::is_dictionary_field(value))
            {
                return values.get(*idx).copied();
            }
            None
        })
    }

    fn is_dictionary_field(term: &Term<'_>) -> bool {
        match term {
            Term::Lam(_) => true,
            Term::Annot(inner, constraint) => {
                matches!(constraint, Term::Pi(..)) || Self::is_dictionary_field(inner)
            }
            Term::Builtin(_) | Term::Global(_) => true,
            _ => false,
        }
    }

    /// Convert `App*(Builtin(name), args...)` to `Variant(enum, idx, args)`.
    pub fn resolve_variant_apps(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // Try top-level first
        if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(t)
            && args.len() == field_specs.len()
        {
            let v = self
                .arena
                .variant(uname, idx, self.arena.alloc_slice(&args));
            // Recurse into payload to resolve nested constructors
            return self.resolve_variant_apps(v);
        }
        self.arena.map(t, &|node| {
            if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(node)
                && args.len() == field_specs.len()
            {
                let v = self
                    .arena
                    .variant(uname, idx, self.arena.alloc_slice(&args));
                return Some(self.resolve_variant_apps(v));
            }
            None
        })
    }

    /// Unwrap an App chain to find a variant constructor and collect its args.
    pub fn collect_variant_args(&self, t: &'bump Term<'bump>) -> Option<VariantWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Global(name) = current
            && let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
        {
            return Some((uname, idx, field_specs, args));
        }
        None
    }

    /// Convert `App*(Named("name.mk"), args...)` to `StructCons(name, args)`.
    pub fn resolve_struct_ctors(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Some((sname, field_specs, args)) = self.collect_struct_args(t)
            && args.len() == field_specs.len()
        {
            let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
            return self.resolve_struct_ctors(sc);
        }
        self.arena.map(t, &|node| {
            if let Some((sname, field_specs, args)) = self.collect_struct_args(node)
                && args.len() == field_specs.len()
            {
                let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
                return Some(self.resolve_struct_ctors(sc));
            }
            None
        })
    }

    /// Unwrap an App chain to find a struct constructor (Name.mk) and collect its args.
    pub fn collect_struct_args(&self, t: &'bump Term<'bump>) -> Option<StructWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Global(name) = current
            && let Some((sname, field_specs)) = self.checker.lookup_struct_ctor(name)
        {
            return Some((sname, field_specs, args));
        }
        None
    }

    /// Convert `App(Builtin("Name.field"), arg)` to `StructProj(arg, idx)`.
    pub fn resolve_struct_projs(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::App(f, arg) = node
                && let Term::Builtin(name) | Term::Global(name) = f
                && let Some(idx) = self.checker.lookup_struct_proj(name)
            {
                let arg = self.resolve_struct_ctors(self.resolve_struct_projs(arg));
                return Some(self.arena.struct_proj(arg, idx));
            }
            None
        })
    }
}
