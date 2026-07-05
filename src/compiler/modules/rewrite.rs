use super::*;

impl<'bump> Compiler<'bump> {
    pub(super) fn rewrite_module(
        &self,
        module: &ParsedModule<'bump>,
        exports: &HashMap<ModuleId, HashMap<String, String>>,
        graph: &PackageModuleGraph,
    ) -> Result<Vec<TopLevel<'bump>>, Diagnostic> {
        let mut imports = HashMap::new();
        if should_auto_import_std_prelude(&module.id, graph) {
            let prelude = standard_prelude_module();
            let prelude_exports = exports.get(&prelude).ok_or_else(|| {
                Diagnostic::new(format!("module not found: {}", display_module(&prelude)))
            })?;
            for (exported, target) in prelude_exports {
                insert_import(
                    &mut imports,
                    prelude.local_symbol_name(exported),
                    target.clone(),
                )?;
            }
        }
        for import in module_imports(&module.tops) {
            for tree in import.trees {
                if tree.wildcard {
                    if is_namespace_wildcard_path(tree.path) {
                        let (dep, prefix) = module.id.namespace_import_prefix(tree.path, graph)?;
                        let dep_exports = exports.get(&dep).ok_or_else(|| {
                            Diagnostic::new(format!("module not found: {}", display_module(&dep)))
                        })?;
                        let prefix_with_sep = format!("{prefix}::");
                        for (exported, target) in dep_exports {
                            let Some(local) = exported.strip_prefix(&prefix_with_sep) else {
                                continue;
                            };
                            if local.contains("::") {
                                continue;
                            }
                            insert_import(&mut imports, local.to_string(), target.clone())?;
                        }
                    } else {
                        let dep = module.id.wildcard_module_import(tree.path, graph)?;
                        let dep_exports = exports.get(&dep).ok_or_else(|| {
                            Diagnostic::new(format!("module not found: {}", display_module(&dep)))
                        })?;
                        for (exported, target) in dep_exports {
                            insert_import(
                                &mut imports,
                                dep.local_symbol_name(exported),
                                target.clone(),
                            )?;
                        }
                    }
                    continue;
                }
                let (dep, full) = module
                    .id
                    .import_symbol_or_namespace_symbol(tree.path, graph)?;
                let dep_exports = exports.get(&dep).ok_or_else(|| {
                    Diagnostic::new(format!("module not found: {}", display_module(&dep)))
                })?;
                if let Some(target) = dep_exports.get(&full) {
                    let local = tree
                        .alias
                        .map(|a| a.to_string())
                        .unwrap_or_else(|| tree.path.last().unwrap().to_string());
                    insert_import(&mut imports, local, target.clone())?;
                    continue;
                }
                if let Some((dep, prefix, local_ns)) =
                    module.id.try_namespace_import(tree.path, graph)?
                {
                    let dep_exports = exports.get(&dep).ok_or_else(|| {
                        Diagnostic::new(format!("module not found: {}", display_module(&dep)))
                    })?;
                    let prefix_with_sep = format!("{prefix}::");
                    for (exported, target) in dep_exports {
                        let Some(local) = exported.strip_prefix(&prefix_with_sep) else {
                            continue;
                        };
                        if local.contains("::") {
                            continue;
                        }
                        insert_import(
                            &mut imports,
                            format!("{local_ns}::{local}"),
                            target.clone(),
                        )?;
                    }
                    continue;
                } else {
                    return Err(Diagnostic::new(format!(
                        "cannot import private or unknown symbol `{full}`"
                    )));
                }
            }
        }
        imports.extend(qualified_term_names(
            &module.id,
            &module.tops,
            graph,
            exports,
        )?);
        let own_names = declared_symbols(&module.tops, &module.id, false)
            .into_iter()
            .map(|(symbol, target)| {
                let local = module.id.local_symbol_name(&symbol);
                (local, target)
            })
            .collect::<HashMap<_, _>>();
        let mut out = Vec::new();
        for top in &module.tops {
            let (top, _public) = unwrap_public(top);
            match top {
                TopLevel::TLDef(name, params, ret, body, span) => {
                    let qname = self.arena.alloc_str(&module.id.join_symbol(name));
                    let mut scope = RewriteScope::default();
                    for (pn, _) in params.iter().rev() {
                        scope.push(pn);
                    }
                    let params = self.rewrite_module_params(
                        params,
                        &imports,
                        &own_names,
                        &mut RewriteScope::default(),
                    );
                    let ret =
                        ret.map(|t| self.rewrite_module_term(t, &imports, &own_names, &mut scope));
                    let body = self.rewrite_module_term(body, &imports, &own_names, &mut scope);
                    out.push(TopLevel::TLDef(qname, params, ret, body, span.clone()));
                }
                TopLevel::TLExternDef(name, params, ret, span) => {
                    let mut scope = RewriteScope::default();
                    for (pn, _) in params.iter().rev() {
                        scope.push(pn);
                    }
                    let params = self.rewrite_module_params(
                        params,
                        &imports,
                        &own_names,
                        &mut RewriteScope::default(),
                    );
                    let ret = self.rewrite_module_term(ret, &imports, &own_names, &mut scope);
                    out.push(TopLevel::TLExternDef(name, params, ret, span.clone()));
                }
                TopLevel::TLInstance(name, constraint, value, span) => {
                    let qname = self.arena.alloc_str(&module.id.join_symbol(name));
                    out.push(TopLevel::TLInstance(
                        qname,
                        self.rewrite_module_term(
                            constraint,
                            &imports,
                            &own_names,
                            &mut RewriteScope::default(),
                        ),
                        self.rewrite_module_term(
                            value,
                            &imports,
                            &own_names,
                            &mut RewriteScope::default(),
                        ),
                        span.clone(),
                    ));
                }
                TopLevel::TLVariable(params, span) => {
                    let params = self.rewrite_module_params(
                        params,
                        &imports,
                        &own_names,
                        &mut RewriteScope::default(),
                    );
                    out.push(TopLevel::TLVariable(params, span.clone()));
                }
                TopLevel::TLTheorem(name, prop, body, span) => {
                    let qname = self.arena.alloc_str(&module.id.join_symbol(name));
                    let prop = self.rewrite_module_term(
                        prop,
                        &imports,
                        &own_names,
                        &mut RewriteScope::default(),
                    );
                    let body = self.rewrite_module_term(
                        body,
                        &imports,
                        &own_names,
                        &mut RewriteScope::default(),
                    );
                    out.push(TopLevel::TLTheorem(qname, prop, body, span.clone()));
                }
                TopLevel::TLCheck(term, constraint, span) => {
                    out.push(TopLevel::TLCheck(
                        self.rewrite_module_term(
                            term,
                            &imports,
                            &own_names,
                            &mut RewriteScope::default(),
                        ),
                        self.rewrite_module_term(
                            constraint,
                            &imports,
                            &own_names,
                            &mut RewriteScope::default(),
                        ),
                        span.clone(),
                    ));
                }
                TopLevel::TLEval(term, span) => {
                    out.push(TopLevel::TLEval(
                        self.rewrite_module_term(
                            term,
                            &imports,
                            &own_names,
                            &mut RewriteScope::default(),
                        ),
                        span.clone(),
                    ));
                }
                TopLevel::TLExpr(term, span) => {
                    out.push(TopLevel::TLExpr(
                        self.rewrite_module_term(
                            term,
                            &imports,
                            &own_names,
                            &mut RewriteScope::default(),
                        ),
                        span.clone(),
                    ));
                }
                TopLevel::TLSplice(term, span) => {
                    out.push(TopLevel::TLSplice(
                        self.rewrite_module_term(
                            term,
                            &imports,
                            &own_names,
                            &mut RewriteScope::default(),
                        ),
                        span.clone(),
                    ));
                }
                TopLevel::TLUse(..)
                | TopLevel::TLMod(..)
                | TopLevel::TLPublic(_)
                | TopLevel::TLAttributed(..) => {}
                TopLevel::TLNamespace(name, items, _) => {
                    self.rewrite_namespace_items(
                        &module.id, name, items, &imports, &own_names, &mut out,
                    )?;
                }
            }
        }
        Ok(out)
    }

    fn rewrite_namespace_items(
        &self,
        module_id: &ModuleId,
        namespace: Name<'bump>,
        items: &'bump [TopLevel<'bump>],
        imports: &HashMap<String, String>,
        own_names: &HashMap<String, String>,
        out: &mut Vec<TopLevel<'bump>>,
    ) -> Result<(), Diagnostic> {
        for item in items {
            let (item, _) = unwrap_public(item);
            match item {
                TopLevel::TLDef(name, params, ret, body, span) => {
                    let logical = format!("{namespace}::{name}");
                    let qname = self.arena.alloc_str(&module_id.join_symbol(&logical));
                    let mut scope = RewriteScope::default();
                    for (pn, _) in params.iter().rev() {
                        scope.push(pn);
                    }
                    let params = self.rewrite_module_params(
                        params,
                        imports,
                        own_names,
                        &mut RewriteScope::default(),
                    );
                    let ret =
                        ret.map(|t| self.rewrite_module_term(t, imports, own_names, &mut scope));
                    let body = self.rewrite_module_term(body, imports, own_names, &mut scope);
                    out.push(TopLevel::TLDef(qname, params, ret, body, span.clone()));
                }
                TopLevel::TLExternDef(name, params, ret, span) => {
                    let logical = format!("{namespace}::{name}");
                    let qname = self.arena.alloc_str(&module_id.join_symbol(&logical));
                    let mut scope = RewriteScope::default();
                    for (pn, _) in params.iter().rev() {
                        scope.push(pn);
                    }
                    let params = self.rewrite_module_params(
                        params,
                        imports,
                        own_names,
                        &mut RewriteScope::default(),
                    );
                    let ret = self.rewrite_module_term(ret, imports, own_names, &mut scope);
                    out.push(TopLevel::TLExternDef(qname, params, ret, span.clone()));
                }
                TopLevel::TLTheorem(name, prop, body, span) => {
                    let logical = format!("{namespace}::{name}");
                    let qname = self.arena.alloc_str(&module_id.join_symbol(&logical));
                    out.push(TopLevel::TLTheorem(
                        qname,
                        self.rewrite_module_term(
                            prop,
                            imports,
                            own_names,
                            &mut RewriteScope::default(),
                        ),
                        self.rewrite_module_term(
                            body,
                            imports,
                            own_names,
                            &mut RewriteScope::default(),
                        ),
                        span.clone(),
                    ));
                }
                TopLevel::TLUse(..)
                | TopLevel::TLMod(..)
                | TopLevel::TLInstance(..)
                | TopLevel::TLVariable(..)
                | TopLevel::TLCheck(..)
                | TopLevel::TLEval(..)
                | TopLevel::TLExpr(..)
                | TopLevel::TLSplice(..)
                | TopLevel::TLNamespace(..)
                | TopLevel::TLPublic(_)
                | TopLevel::TLAttributed(..) => {}
            }
        }
        Ok(())
    }

    fn rewrite_module_params(
        &self,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        imports: &HashMap<String, String>,
        own_names: &HashMap<String, String>,
        scope: &mut RewriteScope,
    ) -> &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)] {
        let mut rewritten = Vec::new();
        for (name, constraint) in params {
            let constraint =
                constraint.map(|t| self.rewrite_module_term(t, imports, own_names, scope));
            rewritten.push((*name, constraint));
            scope.push(name);
        }
        self.arena.alloc_slice(&rewritten)
    }

    fn rewrite_module_term(
        &self,
        term: &'bump Term<'bump>,
        imports: &HashMap<String, String>,
        own_names: &HashMap<String, String>,
        scope: &mut RewriteScope,
    ) -> &'bump Term<'bump> {
        match term {
            Term::Named(name) | Term::Global(name) => {
                if scope.contains(name) {
                    return term;
                }
                let rewritten = self.rewrite_symbol_name(name, imports, own_names);
                if rewritten == *name {
                    term
                } else {
                    self.arena.named(rewritten)
                }
            }
            Term::Builtin(_) => term,
            Term::App(f, a) => self.arena.app(
                self.rewrite_module_term(f, imports, own_names, scope),
                self.rewrite_module_term(a, imports, own_names, scope),
            ),
            Term::Implicit(inner) => self
                .arena
                .implicit(self.rewrite_module_term(inner, imports, own_names, scope)),
            Term::NamedLam(name, body) => {
                scope.push(name);
                let body = self.rewrite_module_term(body, imports, own_names, scope);
                scope.pop();
                self.arena.named_lam(name, body)
            }
            Term::Lam(body) => self
                .arena
                .lam(self.rewrite_module_term(body, imports, own_names, scope)),
            Term::Pi(name, a, b) => {
                let a = self.rewrite_module_term(a, imports, own_names, scope);
                scope.push(name);
                let b = self.rewrite_module_term(b, imports, own_names, scope);
                scope.pop();
                self.arena.pi(name, a, b)
            }
            Term::Let(name, val, body, constraint) => {
                let val = self.rewrite_module_term(val, imports, own_names, scope);
                let constraint =
                    constraint.map(|c| self.rewrite_module_term(c, imports, own_names, scope));
                scope.push(name);
                let body = self.rewrite_module_term(body, imports, own_names, scope);
                scope.pop();
                self.arena.let_(name, val, body, constraint)
            }
            Term::IfThenElse(c, t, f) => self.arena.if_then_else(
                self.rewrite_module_term(c, imports, own_names, scope),
                self.rewrite_module_term(t, imports, own_names, scope),
                self.rewrite_module_term(f, imports, own_names, scope),
            ),
            Term::Refine(name, parent, pred) => {
                let parent = self.rewrite_module_term(parent, imports, own_names, scope);
                scope.push(name);
                let pred = self.rewrite_module_term(pred, imports, own_names, scope);
                scope.pop();
                self.arena.refine(name, parent, pred)
            }
            Term::Annot(inner, constraint) => self.arena.annot(
                self.rewrite_module_term(inner, imports, own_names, scope),
                self.rewrite_module_term(constraint, imports, own_names, scope),
            ),
            Term::ByProof(inner, tactics) => {
                let inner = inner.map(|t| self.rewrite_module_term(t, imports, own_names, scope));
                let tactics = tactics
                    .iter()
                    .map(|t| match t {
                        Tactic::Exact(t) => {
                            Tactic::Exact(self.rewrite_module_term(t, imports, own_names, scope))
                        }
                        Tactic::Apply(t) => {
                            Tactic::Apply(self.rewrite_module_term(t, imports, own_names, scope))
                        }
                        Tactic::Intro(n) => Tactic::Intro(*n),
                        Tactic::Have(n, t) => {
                            Tactic::Have(n, self.rewrite_module_term(t, imports, own_names, scope))
                        }
                        Tactic::Custom(n, args) => {
                            let args = args
                                .iter()
                                .map(|arg| self.rewrite_module_term(arg, imports, own_names, scope))
                                .collect::<Vec<_>>();
                            Tactic::Custom(n, self.arena.alloc_slice(&args))
                        }
                    })
                    .collect::<Vec<_>>();
                self.arena.by_proof(inner, self.arena.alloc_slice(&tactics))
            }
            Term::EnumDef(name, variants) => {
                let qname = self.qualify_type_name(name, own_names);
                let variants = variants
                    .iter()
                    .map(|(vname, fields)| {
                        let qvname = self.qualify_type_name(vname, own_names);
                        let fields = fields
                            .iter()
                            .map(|(fname, c)| {
                                (
                                    *fname,
                                    self.rewrite_module_term(c, imports, own_names, scope),
                                )
                            })
                            .collect::<Vec<_>>();
                        (qvname, self.arena.alloc_slice(&fields))
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .enum_def(qname, self.arena.alloc_slice(&variants))
            }
            Term::StructDef(name, fields) => {
                let qname = self.qualify_type_name(name, own_names);
                let fields = fields
                    .iter()
                    .map(|(fname, c)| {
                        (
                            *fname,
                            self.rewrite_module_term(c, imports, own_names, scope),
                        )
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .struct_def(qname, self.arena.alloc_slice(&fields))
            }
            Term::NamedStructCons(name, fields) => {
                let name = name.map(|name| self.rewrite_symbol_name(name, imports, own_names));
                let fields = fields
                    .iter()
                    .map(|(field, value)| {
                        (
                            *field,
                            self.rewrite_module_term(value, imports, own_names, scope),
                        )
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .named_struct_cons(name, self.arena.alloc_slice(&fields))
            }
            Term::NamedMatch(scrut, branches) => {
                let scrut = self.rewrite_module_term(scrut, imports, own_names, scope);
                let branches = branches
                    .iter()
                    .map(|(variant, binds, body)| {
                        let variant = self.rewrite_symbol_name(variant, imports, own_names);
                        for (name, _) in binds.iter().rev() {
                            scope.push(name);
                        }
                        let body = self.rewrite_module_term(body, imports, own_names, scope);
                        for _ in *binds {
                            scope.pop();
                        }
                        let binds = binds
                            .iter()
                            .map(|(n, c)| {
                                (*n, self.rewrite_module_term(c, imports, own_names, scope))
                            })
                            .collect::<Vec<_>>();
                        (variant, self.arena.alloc_slice(&binds), body)
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .named_match(scrut, self.arena.alloc_slice(&branches))
            }
            Term::Do(stmts) => {
                let stmts = stmts
                    .iter()
                    .map(|stmt| match stmt {
                        crate::core::syntax::DoStmt::Bind(name, rhs) => {
                            crate::core::syntax::DoStmt::Bind(
                                name,
                                self.rewrite_module_term(rhs, imports, own_names, scope),
                            )
                        }
                        crate::core::syntax::DoStmt::Let(name, rhs, constraint) => {
                            let rhs = self.rewrite_module_term(rhs, imports, own_names, scope);
                            let constraint = constraint
                                .map(|c| self.rewrite_module_term(c, imports, own_names, scope));
                            crate::core::syntax::DoStmt::Let(name, rhs, constraint)
                        }
                        crate::core::syntax::DoStmt::Expr(expr) => {
                            crate::core::syntax::DoStmt::Expr(
                                self.rewrite_module_term(expr, imports, own_names, scope),
                            )
                        }
                    })
                    .collect::<Vec<_>>();
                self.arena.do_(self.arena.alloc_slice(&stmts))
            }
            Term::Unsafe(inner) => self
                .arena
                .unsafe_(self.rewrite_module_term(inner, imports, own_names, scope)),
            Term::Pure(inner) => self
                .arena
                .pure(self.rewrite_module_term(inner, imports, own_names, scope)),
            Term::StructProj(subject, idx) => self.arena.struct_proj(
                self.rewrite_module_term(subject, imports, own_names, scope),
                *idx,
            ),
            Term::MethodCall(receiver, method) => self.arena.method_call(
                self.rewrite_module_term(receiver, imports, own_names, scope),
                method,
            ),
            _ => term,
        }
    }

    fn qualify_type_name(
        &self,
        name: Name<'bump>,
        own_names: &HashMap<String, String>,
    ) -> Name<'bump> {
        own_names
            .get(name)
            .map(|q| self.arena.alloc_str(q))
            .unwrap_or(name)
    }

    fn rewrite_symbol_name(
        &self,
        name: Name<'bump>,
        imports: &HashMap<String, String>,
        own_names: &HashMap<String, String>,
    ) -> Name<'bump> {
        if let Some(full) = imports.get(name).or_else(|| own_names.get(name)) {
            return self.arena.alloc_str(full);
        }
        if let Some((prefix, suffix)) = name.rsplit_once("::")
            && let Some(full_prefix) = imports.get(prefix).or_else(|| own_names.get(prefix))
        {
            return self.arena.alloc_str(&format!("{full_prefix}::{suffix}"));
        }
        if let Some((prefix, suffix)) = name.split_once('.')
            && let Some(full_prefix) = imports.get(prefix).or_else(|| own_names.get(prefix))
        {
            return self.arena.alloc_str(&format!("{full_prefix}.{suffix}"));
        }
        name
    }
}
