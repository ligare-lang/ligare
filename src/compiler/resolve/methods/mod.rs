use super::*;

mod helpers;

impl<'bump> Compiler<'bump> {
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

    pub(super) fn constraint_head_and_args(
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

}
