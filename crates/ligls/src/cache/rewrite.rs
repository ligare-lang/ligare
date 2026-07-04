use super::*;

#[derive(Default)]
struct RewriteScope {
    locals: Vec<String>,
}

impl RewriteScope {
    fn contains(&self, name: &str) -> bool {
        self.locals.iter().rev().any(|local| local == name)
    }

    fn push(&mut self, name: &str) {
        self.locals.push(name.to_string());
    }

    fn pop(&mut self) {
        self.locals.pop();
    }
}

pub(super) fn rewrite_top_for_module<'bump>(
    arena: &'bump TermArena<'bump>,
    top: &TopLevel<'bump>,
    imports: &HashMap<String, String>,
    own_names: &HashMap<String, String>,
) -> Vec<TopLevel<'bump>> {
    match unwrap_public(top) {
        TopLevel::TLDef(name, params, ret, body, span) => {
            let qname = own_names.get(*name).map(String::as_str).unwrap_or(name);
            let qname = arena.alloc_str(qname);
            let mut scope = RewriteScope::default();
            for (param, _) in params.iter().rev() {
                scope.push(param);
            }
            let params = rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let ret = ret
                .map(|term| rewrite_term_for_module(arena, term, imports, own_names, &mut scope));
            let body = rewrite_term_for_module(arena, body, imports, own_names, &mut scope);
            vec![TopLevel::TLDef(qname, params, ret, body, span.clone())]
        }
        TopLevel::TLExternDef(name, params, ret, span) => {
            let mut scope = RewriteScope::default();
            for (param, _) in params.iter().rev() {
                scope.push(param);
            }
            let params = rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let ret = rewrite_term_for_module(arena, ret, imports, own_names, &mut scope);
            vec![TopLevel::TLExternDef(name, params, ret, span.clone())]
        }
        TopLevel::TLInstance(name, constraint, value, span) => {
            let qname = own_names.get(*name).map(String::as_str).unwrap_or(name);
            let qname = arena.alloc_str(qname);
            vec![TopLevel::TLInstance(
                qname,
                rewrite_term_for_module(
                    arena,
                    constraint,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                rewrite_term_for_module(
                    arena,
                    value,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                span.clone(),
            )]
        }
        TopLevel::TLVariable(params, span) => vec![TopLevel::TLVariable(
            rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLTheorem(name, prop, body, span) => {
            let qname = own_names.get(*name).map(String::as_str).unwrap_or(name);
            let qname = arena.alloc_str(qname);
            let prop = rewrite_term_for_module(
                arena,
                prop,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let body = rewrite_term_for_module(
                arena,
                body,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            vec![TopLevel::TLTheorem(qname, prop, body, span.clone())]
        }
        TopLevel::TLCheck(term, constraint, span) => vec![TopLevel::TLCheck(
            rewrite_term_for_module(
                arena,
                term,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            rewrite_term_for_module(
                arena,
                constraint,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLEval(term, span) => vec![TopLevel::TLEval(
            rewrite_term_for_module(
                arena,
                term,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLExpr(term, span) => vec![TopLevel::TLExpr(
            rewrite_term_for_module(
                arena,
                term,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLSplice(term, span) => vec![TopLevel::TLSplice(
            rewrite_term_for_module(
                arena,
                term,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLNamespace(name, items, _) => {
            let mut rewritten = Vec::new();
            for item in *items {
                rewrite_namespace_item_for_module(
                    arena,
                    name,
                    item,
                    imports,
                    own_names,
                    &mut rewritten,
                );
            }
            rewritten
        }
        TopLevel::TLUse(..)
        | TopLevel::TLMod(..)
        | TopLevel::TLPublic(_)
        | TopLevel::TLAttributed(..) => Vec::new(),
    }
}

fn rewrite_namespace_item_for_module<'bump>(
    arena: &'bump TermArena<'bump>,
    namespace: &str,
    top: &TopLevel<'bump>,
    imports: &HashMap<String, String>,
    own_names: &HashMap<String, String>,
    out: &mut Vec<TopLevel<'bump>>,
) {
    match unwrap_public(top) {
        TopLevel::TLDef(name, params, ret, body, span) => {
            let local = format!("{namespace}::{name}");
            let qname = own_names
                .get(&local)
                .map(String::as_str)
                .unwrap_or(local.as_str());
            let qname = arena.alloc_str(qname);
            let mut scope = RewriteScope::default();
            for (param, _) in params.iter().rev() {
                scope.push(param);
            }
            let params = rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let ret = ret
                .map(|term| rewrite_term_for_module(arena, term, imports, own_names, &mut scope));
            let body = rewrite_term_for_module(arena, body, imports, own_names, &mut scope);
            out.push(TopLevel::TLDef(qname, params, ret, body, span.clone()));
        }
        TopLevel::TLExternDef(name, params, ret, span) => {
            let local = format!("{namespace}::{name}");
            let qname = own_names
                .get(&local)
                .map(String::as_str)
                .unwrap_or(local.as_str());
            let qname = arena.alloc_str(qname);
            let mut scope = RewriteScope::default();
            for (param, _) in params.iter().rev() {
                scope.push(param);
            }
            let params = rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let ret = rewrite_term_for_module(arena, ret, imports, own_names, &mut scope);
            out.push(TopLevel::TLExternDef(qname, params, ret, span.clone()));
        }
        TopLevel::TLInstance(name, constraint, value, span) => {
            let local = format!("{namespace}::{name}");
            let qname = own_names
                .get(&local)
                .map(String::as_str)
                .unwrap_or(local.as_str());
            let qname = arena.alloc_str(qname);
            out.push(TopLevel::TLInstance(
                qname,
                rewrite_term_for_module(
                    arena,
                    constraint,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                rewrite_term_for_module(
                    arena,
                    value,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                span.clone(),
            ));
        }
        TopLevel::TLVariable(params, span) => {
            out.push(TopLevel::TLVariable(
                rewrite_params_for_module(
                    arena,
                    params,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                span.clone(),
            ));
        }
        TopLevel::TLTheorem(name, prop, body, span) => {
            let local = format!("{namespace}::{name}");
            let qname = own_names
                .get(&local)
                .map(String::as_str)
                .unwrap_or(local.as_str());
            let qname = arena.alloc_str(qname);
            out.push(TopLevel::TLTheorem(
                qname,
                rewrite_term_for_module(
                    arena,
                    prop,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                rewrite_term_for_module(
                    arena,
                    body,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                span.clone(),
            ));
        }
        _ => {}
    }
}

fn rewrite_params_for_module<'bump>(
    arena: &'bump TermArena<'bump>,
    params: &'bump [(&'bump str, Option<&'bump Term<'bump>>)],
    imports: &HashMap<String, String>,
    own_names: &HashMap<String, String>,
    scope: &mut RewriteScope,
) -> &'bump [(&'bump str, Option<&'bump Term<'bump>>)] {
    let mut rewritten = Vec::new();
    for (name, constraint) in params {
        let constraint =
            constraint.map(|term| rewrite_term_for_module(arena, term, imports, own_names, scope));
        rewritten.push((*name, constraint));
        scope.push(name);
    }
    arena.alloc_slice(&rewritten)
}

fn rewrite_term_for_module<'bump>(
    arena: &'bump TermArena<'bump>,
    term: &'bump Term<'bump>,
    imports: &HashMap<String, String>,
    own_names: &HashMap<String, String>,
    scope: &mut RewriteScope,
) -> &'bump Term<'bump> {
    match term {
        Term::Named(name) => {
            if scope.contains(name) {
                return term;
            }
            if let Some(full) = imports.get(*name).or_else(|| own_names.get(*name)) {
                return arena.named(arena.alloc_str(full));
            }
            term
        }
        Term::Builtin(_) | Term::Global(_) => term,
        Term::App(f, a) => arena.app(
            rewrite_term_for_module(arena, f, imports, own_names, scope),
            rewrite_term_for_module(arena, a, imports, own_names, scope),
        ),
        Term::Implicit(inner) => arena.implicit(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::NamedLam(name, body) => {
            scope.push(name);
            let body = rewrite_term_for_module(arena, body, imports, own_names, scope);
            scope.pop();
            arena.named_lam(name, body)
        }
        Term::Lam(body) => arena.lam(rewrite_term_for_module(
            arena, body, imports, own_names, scope,
        )),
        Term::Pi(name, a, b) => {
            let a = rewrite_term_for_module(arena, a, imports, own_names, scope);
            scope.push(name);
            let b = rewrite_term_for_module(arena, b, imports, own_names, scope);
            scope.pop();
            arena.pi(name, a, b)
        }
        Term::Let(name, value, body, constraint) => {
            let value = rewrite_term_for_module(arena, value, imports, own_names, scope);
            let constraint = constraint
                .map(|term| rewrite_term_for_module(arena, term, imports, own_names, scope));
            scope.push(name);
            let body = rewrite_term_for_module(arena, body, imports, own_names, scope);
            scope.pop();
            arena.let_(name, value, body, constraint)
        }
        Term::IfThenElse(cond, then_branch, else_branch) => arena.if_then_else(
            rewrite_term_for_module(arena, cond, imports, own_names, scope),
            rewrite_term_for_module(arena, then_branch, imports, own_names, scope),
            rewrite_term_for_module(arena, else_branch, imports, own_names, scope),
        ),
        Term::Refine(name, parent, predicate) => {
            let parent = rewrite_term_for_module(arena, parent, imports, own_names, scope);
            scope.push(name);
            let predicate = rewrite_term_for_module(arena, predicate, imports, own_names, scope);
            scope.pop();
            arena.refine(name, parent, predicate)
        }
        Term::Annot(inner, constraint) => arena.annot(
            rewrite_term_for_module(arena, inner, imports, own_names, scope),
            rewrite_term_for_module(arena, constraint, imports, own_names, scope),
        ),
        Term::ByProof(inner, tactics) => {
            let inner =
                inner.map(|term| rewrite_term_for_module(arena, term, imports, own_names, scope));
            let tactics = tactics
                .iter()
                .map(|tactic| match tactic {
                    Tactic::Exact(term) => Tactic::Exact(rewrite_term_for_module(
                        arena, term, imports, own_names, scope,
                    )),
                    Tactic::Apply(term) => Tactic::Apply(rewrite_term_for_module(
                        arena, term, imports, own_names, scope,
                    )),
                    Tactic::Intro(name) => Tactic::Intro(*name),
                    Tactic::Have(name, term) => Tactic::Have(
                        name,
                        rewrite_term_for_module(arena, term, imports, own_names, scope),
                    ),
                    Tactic::Custom(name, args) => {
                        let args = args
                            .iter()
                            .map(|arg| {
                                rewrite_term_for_module(arena, arg, imports, own_names, scope)
                            })
                            .collect::<Vec<_>>();
                        Tactic::Custom(name, arena.alloc_slice(&args))
                    }
                })
                .collect::<Vec<_>>();
            arena.by_proof(inner, arena.alloc_slice(&tactics))
        }
        Term::EnumDef(name, variants) => {
            let qname = qualify_type_name(arena, name, own_names);
            let variants = variants
                .iter()
                .map(|(variant, fields)| {
                    let qvariant = qualify_type_name(arena, variant, own_names);
                    let fields = fields
                        .iter()
                        .map(|(field, constraint)| {
                            (
                                *field,
                                rewrite_term_for_module(
                                    arena, constraint, imports, own_names, scope,
                                ),
                            )
                        })
                        .collect::<Vec<_>>();
                    (qvariant, arena.alloc_slice(&fields))
                })
                .collect::<Vec<_>>();
            arena.enum_def(qname, arena.alloc_slice(&variants))
        }
        Term::StructDef(name, fields) => {
            let qname = qualify_type_name(arena, name, own_names);
            let fields = fields
                .iter()
                .map(|(field, constraint)| {
                    (
                        *field,
                        rewrite_term_for_module(arena, constraint, imports, own_names, scope),
                    )
                })
                .collect::<Vec<_>>();
            arena.struct_def(qname, arena.alloc_slice(&fields))
        }
        Term::Variant(name, index, payloads) => {
            let qname = qualify_type_name(arena, name, own_names);
            let payloads = payloads
                .iter()
                .map(|payload| rewrite_term_for_module(arena, payload, imports, own_names, scope))
                .collect::<Vec<_>>();
            arena.variant(qname, *index, arena.alloc_slice(&payloads))
        }
        Term::StructCons(name, payloads) => {
            let qname = qualify_type_name(arena, name, own_names);
            let payloads = payloads
                .iter()
                .map(|payload| rewrite_term_for_module(arena, payload, imports, own_names, scope))
                .collect::<Vec<_>>();
            arena.struct_cons(qname, arena.alloc_slice(&payloads))
        }
        Term::Match(scrutinee, branches) => {
            let scrutinee = rewrite_term_for_module(arena, scrutinee, imports, own_names, scope);
            let branches = branches
                .iter()
                .map(|(variant, binds, body)| {
                    for (name, _) in binds.iter().rev() {
                        scope.push(name);
                    }
                    let body = rewrite_term_for_module(arena, body, imports, own_names, scope);
                    for _ in *binds {
                        scope.pop();
                    }
                    let binds = binds
                        .iter()
                        .map(|(name, constraint)| {
                            (
                                *name,
                                rewrite_term_for_module(
                                    arena, constraint, imports, own_names, scope,
                                ),
                            )
                        })
                        .collect::<Vec<_>>();
                    (*variant, arena.alloc_slice(&binds), body)
                })
                .collect::<Vec<_>>();
            arena.match_(scrutinee, arena.alloc_slice(&branches))
        }
        Term::NamedMatch(scrutinee, branches) => {
            let scrutinee = rewrite_term_for_module(arena, scrutinee, imports, own_names, scope);
            let branches = branches
                .iter()
                .map(|(variant, binds, body)| {
                    let qvariant = qualify_type_name(arena, variant, own_names);
                    for (name, _) in binds.iter().rev() {
                        scope.push(name);
                    }
                    let body = rewrite_term_for_module(arena, body, imports, own_names, scope);
                    for _ in *binds {
                        scope.pop();
                    }
                    let binds = binds
                        .iter()
                        .map(|(name, constraint)| {
                            (
                                *name,
                                rewrite_term_for_module(
                                    arena, constraint, imports, own_names, scope,
                                ),
                            )
                        })
                        .collect::<Vec<_>>();
                    (qvariant, arena.alloc_slice(&binds), body)
                })
                .collect::<Vec<_>>();
            arena.named_match(scrutinee, arena.alloc_slice(&branches))
        }
        Term::Do(stmts) => {
            let stmts = stmts
                .iter()
                .map(|stmt| match stmt {
                    DoStmt::Bind(name, rhs) => DoStmt::Bind(
                        name,
                        rewrite_term_for_module(arena, rhs, imports, own_names, scope),
                    ),
                    DoStmt::Let(name, rhs, constraint) => {
                        let rhs = rewrite_term_for_module(arena, rhs, imports, own_names, scope);
                        let constraint = constraint.map(|constraint| {
                            rewrite_term_for_module(arena, constraint, imports, own_names, scope)
                        });
                        DoStmt::Let(name, rhs, constraint)
                    }
                    DoStmt::Expr(expr) => DoStmt::Expr(rewrite_term_for_module(
                        arena, expr, imports, own_names, scope,
                    )),
                })
                .collect::<Vec<_>>();
            arena.do_(arena.alloc_slice(&stmts))
        }
        Term::StructProj(inner, index) => arena.struct_proj(
            rewrite_term_for_module(arena, inner, imports, own_names, scope),
            *index,
        ),
        Term::MethodCall(receiver, method) => arena.method_call(
            rewrite_term_for_module(arena, receiver, imports, own_names, scope),
            method,
        ),
        Term::Unsafe(inner) => arena.unsafe_(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::Pure(inner) => arena.pure(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::Quote(inner) => arena.quote(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::Splice(inner) => arena.splice(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::Var(_)
        | Term::LitInt(_)
        | Term::LitBool(_)
        | Term::LitStr(_)
        | Term::PrimOp(_)
        | Term::Universe(_)
        | Term::AutoProof
        | Term::RefParam => term,
    }
}

fn qualify_type_name<'bump>(
    arena: &'bump TermArena<'bump>,
    name: &'bump str,
    own_names: &HashMap<String, String>,
) -> &'bump str {
    own_names
        .get(name)
        .map(|name| arena.alloc_str(name))
        .unwrap_or(name)
}
