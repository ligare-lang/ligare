use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::core::syntax::{Name, Tactic, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::{TopLevel, UseTree, Visibility, parse_program};

use super::{Compiler, read_source_file};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ModuleId(Vec<String>);

impl ModuleId {
    fn root() -> Self {
        Self(Vec::new())
    }

    fn from_path(root: &Path, file: &Path) -> Result<Self, Diagnostic> {
        let rel = file.strip_prefix(root).map_err(|_| {
            Diagnostic::new(format!(
                "module file `{}` is not under module root `{}`",
                file.display(),
                root.display()
            ))
        })?;
        let mut parts = rel
            .with_extension("")
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        if parts == ["main"] {
            parts.clear();
        }
        Ok(Self(parts))
    }

    fn join_symbol(&self, name: &str) -> String {
        if self.0.is_empty() {
            name.to_string()
        } else {
            format!("{}::{name}", self.0.join("::"))
        }
    }

    fn from_import_path(path: &[Name<'_>]) -> Self {
        Self(
            path[..path.len().saturating_sub(1)]
                .iter()
                .map(|p| (*p).to_string())
                .collect(),
        )
    }

    fn symbol_from_import_path(path: &[Name<'_>]) -> Option<String> {
        let item = path.last()?;
        let module = Self::from_import_path(path);
        Some(module.join_symbol(item))
    }
}

#[derive(Clone)]
struct ParsedModule<'bump> {
    id: ModuleId,
    tops: Vec<TopLevel<'bump>>,
}

struct ModuleEnv<'bump> {
    exports: HashMap<ModuleId, HashMap<String, String>>,
    rewritten: HashMap<ModuleId, Vec<TopLevel<'bump>>>,
    order: Vec<ModuleId>,
}

#[derive(Default)]
struct RewriteScope {
    locals: Vec<String>,
}

impl RewriteScope {
    fn contains(&self, name: &str) -> bool {
        self.locals.iter().rev().any(|n| n == name)
    }

    fn push(&mut self, name: &str) {
        self.locals.push(name.to_string());
    }

    fn pop(&mut self) {
        self.locals.pop();
    }
}

pub(crate) fn is_module_entry(file: &str) -> bool {
    Path::new(file)
        .file_name()
        .and_then(|n| n.to_str())
        .is_some_and(|n| n == "main.lig")
}

impl<'bump> Compiler<'bump> {
    pub(crate) fn process_module_entry(&mut self, file: &str) -> Result<(), Diagnostic> {
        let env = self.load_module_graph(file)?;
        for id in env.order {
            let tops = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in tops {
                self.process_top_level(top)?;
            }
        }
        self.validate_module_main()
    }

    pub(crate) fn collect_module_entry(&mut self, file: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        let env = self.load_module_graph(file)?;
        for id in env.order {
            let content = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in &content {
                self.process_top_level(top.clone())?;
            }
            let codegen = self.collect_codegen_state(&content)?;
            let monomorphized = self.monomorphize_for_codegen(content, codegen)?;
            let eraser =
                crate::checker::erase::Eraser::new(self.arena, self.checker.builtins.clone());
            let erased = self.erase_and_collect_tops(monomorphized.tops, &eraser)?;
            self.raw_defs.extend(monomorphized.codegen.raw_defs);
            self.fun_sigs.extend(monomorphized.codegen.fun_sigs);
            self.union_types.extend(monomorphized.codegen.union_types);
            self.struct_types.extend(monomorphized.codegen.struct_types);
            self.tops.extend(erased.tops);
        }
        self.validate_module_main()
    }

    fn load_module_graph(&self, entry: &str) -> Result<ModuleEnv<'bump>, Diagnostic> {
        let entry_path = PathBuf::from(entry);
        let root = entry_path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from("."));
        let mut parsed = HashMap::new();
        self.load_module(&root, entry_path, &mut parsed)?;
        let root_module = parsed
            .get(&ModuleId::root())
            .ok_or_else(|| Diagnostic::new("entry module `main.lig` was not loaded"))?;
        if !has_public_main(&root_module.tops) {
            return Err(Diagnostic::new(
                "entry module `main.lig` must define `pub main : IO Unit`",
            ));
        }
        let exports = self.collect_exports(&parsed)?;
        let mut env = ModuleEnv {
            exports,
            rewritten: HashMap::new(),
            order: Vec::new(),
        };
        let mut visiting = Vec::new();
        let mut done = HashSet::new();
        self.visit_module(
            &ModuleId::root(),
            &root,
            &parsed,
            &mut env,
            &mut visiting,
            &mut done,
        )?;
        Ok(env)
    }

    fn load_module(
        &self,
        root: &Path,
        file: PathBuf,
        parsed: &mut HashMap<ModuleId, ParsedModule<'bump>>,
    ) -> Result<ModuleId, Diagnostic> {
        let id = ModuleId::from_path(root, &file)?;
        if parsed.contains_key(&id) {
            return Ok(id);
        }
        let file_str = file.to_string_lossy().into_owned();
        let source = read_source_file(&file_str)?;
        let tops = parse_program(&source, self.bump, self.arena)
            .map_err(|e| Diagnostic::with_span(format!("parse error: {}", e.message), e.span))
            .map_err(|d| d.with_source(&file_str, &source))?;
        parsed.insert(
            id.clone(),
            ParsedModule {
                id: id.clone(),
                tops: tops.clone(),
            },
        );
        for module in import_deps(&tops)? {
            let dep_file = module_path(root, &module);
            if !dep_file.exists() {
                return Err(Diagnostic::new(format!(
                    "module not found: {} at {}",
                    module.0.join("::"),
                    dep_file.display()
                )));
            }
            self.load_module(root, dep_file, parsed)?;
        }
        Ok(id)
    }

    fn collect_exports(
        &self,
        parsed: &HashMap<ModuleId, ParsedModule<'bump>>,
    ) -> Result<HashMap<ModuleId, HashMap<String, String>>, Diagnostic> {
        let mut direct = HashMap::new();
        for (id, module) in parsed {
            let public_names = declared_names(&module.tops, true);
            let rewritten = public_names
                .iter()
                .map(|name| {
                    let symbol = id.join_symbol(name);
                    (symbol.clone(), symbol)
                })
                .collect::<HashMap<_, _>>();
            direct.insert(id.clone(), rewritten);
        }
        let mut exports = direct.clone();
        let mut changed = true;
        while changed {
            changed = false;
            for (id, module) in parsed {
                let mut set = exports.get(id).cloned().unwrap_or_default();
                for import in module_imports(&module.tops) {
                    if import.visibility != Visibility::Public {
                        continue;
                    }
                    for tree in import.trees {
                        let requested =
                            ModuleId::symbol_from_import_path(tree.path).ok_or_else(|| {
                                Diagnostic::new("pub use path must include a module and symbol")
                            })?;
                        let dep = ModuleId::from_import_path(tree.path);
                        let dep_exports = exports.get(&dep).ok_or_else(|| {
                            Diagnostic::new(format!("module not found: {}", dep.0.join("::")))
                        })?;
                        let Some(target) = dep_exports.get(&requested) else {
                            return Err(Diagnostic::new(format!(
                                "cannot re-export private or unknown symbol `{requested}`"
                            )));
                        };
                        let local = tree
                            .alias
                            .map(|a| a.to_string())
                            .unwrap_or_else(|| tree.path.last().unwrap().to_string());
                        let exported = id.join_symbol(&local);
                        if set.insert(exported, target.clone()).is_none() {
                            changed = true;
                        }
                    }
                }
                exports.insert(id.clone(), set);
            }
        }
        Ok(exports)
    }

    fn visit_module(
        &self,
        id: &ModuleId,
        root: &Path,
        parsed: &HashMap<ModuleId, ParsedModule<'bump>>,
        env: &mut ModuleEnv<'bump>,
        visiting: &mut Vec<ModuleId>,
        done: &mut HashSet<ModuleId>,
    ) -> Result<(), Diagnostic> {
        if done.contains(id) {
            return Ok(());
        }
        if let Some(pos) = visiting.iter().position(|m| m == id) {
            let mut cycle = visiting[pos..]
                .iter()
                .map(|m| display_module(m))
                .collect::<Vec<_>>();
            cycle.push(display_module(id));
            return Err(Diagnostic::new(format!(
                "cyclic module dependency: {}",
                cycle.join(" -> ")
            )));
        }
        visiting.push(id.clone());
        let module = parsed
            .get(id)
            .ok_or_else(|| Diagnostic::new(format!("module not found: {}", display_module(id))))?;
        for dep in import_deps(&module.tops)? {
            let dep_file = module_path(root, &dep);
            if !parsed.contains_key(&dep) || !dep_file.exists() {
                return Err(Diagnostic::new(format!(
                    "module not found: {} at {}",
                    display_module(&dep),
                    dep_file.display()
                )));
            }
            self.visit_module(&dep, root, parsed, env, visiting, done)?;
        }
        visiting.pop();
        let rewritten = self.rewrite_module(module, &env.exports)?;
        env.rewritten.insert(id.clone(), rewritten);
        env.order.push(id.clone());
        done.insert(id.clone());
        Ok(())
    }

    fn rewrite_module(
        &self,
        module: &ParsedModule<'bump>,
        exports: &HashMap<ModuleId, HashMap<String, String>>,
    ) -> Result<Vec<TopLevel<'bump>>, Diagnostic> {
        let mut imports = HashMap::new();
        for import in module_imports(&module.tops) {
            for tree in import.trees {
                let full = ModuleId::symbol_from_import_path(tree.path)
                    .ok_or_else(|| Diagnostic::new("use path must include a module and symbol"))?;
                let dep = ModuleId::from_import_path(tree.path);
                let dep_exports = exports.get(&dep).ok_or_else(|| {
                    Diagnostic::new(format!("module not found: {}", display_module(&dep)))
                })?;
                let Some(target) = dep_exports.get(&full) else {
                    return Err(Diagnostic::new(format!(
                        "cannot import private or unknown symbol `{full}`"
                    )));
                };
                let local = tree
                    .alias
                    .map(|a| a.to_string())
                    .unwrap_or_else(|| tree.path.last().unwrap().to_string());
                imports.insert(local, target.clone());
            }
        }
        let own_names = declared_names(&module.tops, false)
            .into_iter()
            .map(|name| (name.clone(), module.id.join_symbol(&name)))
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
                TopLevel::TLShow(term, span) => {
                    out.push(TopLevel::TLShow(
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
                TopLevel::TLUse(..) | TopLevel::TLPublic(_) => {}
            }
        }
        Ok(out)
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
            Term::Named(name) => {
                if scope.contains(name) {
                    return term;
                }
                if let Some(full) = imports.get(*name).or_else(|| own_names.get(*name)) {
                    return self.arena.named(self.arena.alloc_str(full));
                }
                term
            }
            Term::Builtin(_) | Term::Global(_) => term,
            Term::App(f, a) => self.arena.app(
                self.rewrite_module_term(f, imports, own_names, scope),
                self.rewrite_module_term(a, imports, own_names, scope),
            ),
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
                    })
                    .collect::<Vec<_>>();
                self.arena.by_proof(inner, self.arena.alloc_slice(&tactics))
            }
            Term::UnionDef(name, variants) => {
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
                    .union_def(qname, self.arena.alloc_slice(&variants))
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
            Term::NamedMatch(scrut, branches) => {
                let scrut = self.rewrite_module_term(scrut, imports, own_names, scope);
                let branches = branches
                    .iter()
                    .map(|(variant, binds, body)| {
                        let variant = self.qualify_type_name(variant, own_names);
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

    fn validate_module_main(&self) -> Result<(), Diagnostic> {
        if !self.env.contains_key("main") {
            return Err(Diagnostic::new(
                "entry module `main.lig` must define `pub main : IO Unit`",
            ));
        }
        Ok(())
    }
}

struct ImportItem<'a, 'bump> {
    trees: &'a [UseTree<'bump>],
    visibility: Visibility,
}

fn module_imports<'a, 'bump>(tops: &'a [TopLevel<'bump>]) -> Vec<ImportItem<'a, 'bump>> {
    tops.iter()
        .filter_map(|top| match unwrap_public(top).0 {
            TopLevel::TLUse(trees, visibility, _) => Some(ImportItem {
                trees,
                visibility: visibility.clone(),
            }),
            _ => None,
        })
        .collect()
}

fn import_deps<'bump>(tops: &[TopLevel<'bump>]) -> Result<Vec<ModuleId>, Diagnostic> {
    let mut deps = Vec::new();
    let mut seen = HashSet::new();
    for import in module_imports(tops) {
        for tree in import.trees {
            if tree.path.len() < 2 {
                return Err(Diagnostic::new("use path must include a module and symbol"));
            }
            let dep = ModuleId::from_import_path(tree.path);
            if seen.insert(dep.clone()) {
                deps.push(dep);
            }
        }
    }
    Ok(deps)
}

fn declared_names<'bump>(tops: &[TopLevel<'bump>], public_only: bool) -> HashSet<String> {
    tops.iter()
        .filter_map(|top| {
            let (top, public) = unwrap_public(top);
            if public_only && !public {
                return None;
            }
            match top {
                TopLevel::TLDef(name, ..) | TopLevel::TLTheorem(name, ..) => Some(name.to_string()),
                _ => None,
            }
        })
        .collect()
}

fn has_public_main<'bump>(tops: &[TopLevel<'bump>]) -> bool {
    tops.iter().any(|top| {
        let (top, public) = unwrap_public(top);
        public && matches!(top, TopLevel::TLDef(name, ..) if *name == "main")
    })
}

fn unwrap_public<'a, 'bump>(top: &'a TopLevel<'bump>) -> (&'a TopLevel<'bump>, bool) {
    match top {
        TopLevel::TLPublic(inner) => (inner, true),
        other => (other, false),
    }
}

fn module_path(root: &Path, module: &ModuleId) -> PathBuf {
    let mut path = root.to_path_buf();
    for part in &module.0 {
        path.push(part);
    }
    path.set_extension("lig");
    path
}

fn display_module(module: &ModuleId) -> String {
    if module.0.is_empty() {
        "main".into()
    } else {
        module.0.join("::")
    }
}
