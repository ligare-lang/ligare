use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::core::syntax::{Name, Tactic, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::{TopLevel, UseTree, Visibility, parse_program};

use super::{Compiler, read_source_file};

#[derive(Clone, Debug, Default)]
pub struct PackageModuleGraph {
    pub root_deps: HashSet<String>,
    pub packages: HashMap<String, PackageModuleInfo>,
}

#[derive(Clone, Debug)]
pub struct PackageModuleInfo {
    pub root: PathBuf,
    pub deps: HashSet<String>,
    pub public_modules: HashSet<Vec<String>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ModuleId {
    package: Option<String>,
    path: Vec<String>,
}

impl ModuleId {
    fn root() -> Self {
        Self {
            package: None,
            path: Vec::new(),
        }
    }

    fn from_path(package: Option<String>, root: &Path, file: &Path) -> Result<Self, Diagnostic> {
        let rel = file.strip_prefix(root).map_err(|_| {
            Diagnostic::new(format!(
                "module file `{}` is not under module root `{}`",
                file.display(),
                root.display()
            ))
        })?;
        let mut path = rel
            .with_extension("")
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>();
        if path == ["main"] {
            path.clear();
        }
        Ok(Self { package, path })
    }

    fn package(package: &str, path: Vec<String>) -> Self {
        Self {
            package: Some(package.to_string()),
            path,
        }
    }

    fn join_symbol(&self, name: &str) -> String {
        let mut parts = Vec::new();
        if let Some(package) = &self.package {
            parts.push(package.clone());
        }
        parts.extend(self.path.clone());
        if parts.is_empty() {
            name.to_string()
        } else {
            format!("{}::{name}", parts.join("::"))
        }
    }

    fn local_import_path(&self, path: &[Name<'_>]) -> Self {
        Self {
            package: self.package.clone(),
            path: path[..path.len().saturating_sub(1)]
                .iter()
                .map(|p| (*p).to_string())
                .collect(),
        }
    }

    fn symbol_from_import_path(
        &self,
        path: &[Name<'_>],
        graph: &PackageModuleGraph,
    ) -> Option<String> {
        let item = path.last()?;
        let module = self.resolve_import_module(path, graph).ok()?;
        Some(module.join_symbol(item))
    }

    fn resolve_import_module(
        &self,
        path: &[Name<'_>],
        graph: &PackageModuleGraph,
    ) -> Result<Self, Diagnostic> {
        if path.len() < 2 {
            return Err(Diagnostic::new("use path must include a module and symbol"));
        }
        let first = path[0].to_string();
        let accessible = match &self.package {
            None => graph.root_deps.contains(&first),
            Some(package) => graph
                .packages
                .get(package)
                .is_some_and(|info| info.deps.contains(&first)),
        };
        if accessible {
            if path.len() < 3 {
                return Err(Diagnostic::new(
                    "package use path must be `package::module::symbol`",
                ));
            }
            let module_path = path[1..path.len() - 1]
                .iter()
                .map(|p| (*p).to_string())
                .collect::<Vec<_>>();
            let info = graph.packages.get(&first).ok_or_else(|| {
                Diagnostic::new(format!("package dependency `{first}` was not resolved"))
            })?;
            if !info.public_modules.contains(&module_path) {
                return Err(Diagnostic::new(format!(
                    "module `{}` is not exported by package `{first}`",
                    module_path.join("::")
                )));
            }
            return Ok(Self::package(&first, module_path));
        }
        Ok(self.local_import_path(path))
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

pub(crate) fn source_uses_modules(source: &str) -> bool {
    source.lines().any(|line| {
        let line = line.trim_start();
        line.starts_with("use ") || line.starts_with("pub use ")
    })
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

    pub fn process_project_entry(
        &mut self,
        root: &Path,
        entry: &Path,
        graph: PackageModuleGraph,
    ) -> Result<(), Diagnostic> {
        let env = self.load_project_module_graph(root, entry, graph)?;
        for id in env.order {
            let tops = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in tops {
                self.process_top_level(top)?;
            }
        }
        self.validate_module_main()
    }

    pub fn collect_project_entry(
        &mut self,
        root: &Path,
        entry: &Path,
        graph: PackageModuleGraph,
    ) -> Result<(), Diagnostic> {
        self.quiet = true;
        let env = self.load_project_module_graph(root, entry, graph)?;
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
        self.load_project_module_graph(&root, &entry_path, PackageModuleGraph::default())
    }

    fn load_project_module_graph(
        &self,
        root: &Path,
        entry_path: &Path,
        graph: PackageModuleGraph,
    ) -> Result<ModuleEnv<'bump>, Diagnostic> {
        let module_root = entry_path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| root.to_path_buf());
        let mut parsed = HashMap::new();
        self.load_module_as(
            &module_root,
            entry_path.to_path_buf(),
            ModuleId::root(),
            &graph,
            &mut parsed,
        )?;
        let entry_id = ModuleId::root();
        let root_module = parsed
            .get(&entry_id)
            .ok_or_else(|| Diagnostic::new("entry module was not loaded"))?;
        if entry_id == ModuleId::root() && !has_public_main(&root_module.tops) {
            return Err(Diagnostic::new(format!(
                "entry module `{}` must define `pub main : IO Unit`",
                entry_path.display()
            )));
        }
        let exports = self.collect_exports(&parsed, &graph)?;
        let mut env = ModuleEnv {
            exports,
            rewritten: HashMap::new(),
            order: Vec::new(),
        };
        let mut visiting = Vec::new();
        let mut done = HashSet::new();
        self.visit_module(
            &entry_id,
            &module_root,
            &graph,
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
        graph: &PackageModuleGraph,
        parsed: &mut HashMap<ModuleId, ParsedModule<'bump>>,
    ) -> Result<ModuleId, Diagnostic> {
        let id = ModuleId::from_path(None, root, &file)?;
        self.load_module_as(root, file, id, graph, parsed)
    }

    fn load_module_as(
        &self,
        root: &Path,
        file: PathBuf,
        id: ModuleId,
        graph: &PackageModuleGraph,
        parsed: &mut HashMap<ModuleId, ParsedModule<'bump>>,
    ) -> Result<ModuleId, Diagnostic> {
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
        for module in import_deps(&id, &tops, graph)? {
            let (dep_root, dep_file) = module_file(root, &module, graph)?;
            if !dep_file.exists() {
                return Err(Diagnostic::new(format!(
                    "module not found: {} at {}",
                    display_module(&module),
                    dep_file.display()
                )));
            }
            if module.package.is_some() {
                self.load_module_as(&dep_root, dep_file, module, graph, parsed)?;
            } else {
                self.load_module(&dep_root, dep_file, graph, parsed)?;
            }
        }
        Ok(id)
    }

    fn collect_exports(
        &self,
        parsed: &HashMap<ModuleId, ParsedModule<'bump>>,
        graph: &PackageModuleGraph,
    ) -> Result<HashMap<ModuleId, HashMap<String, String>>, Diagnostic> {
        let mut direct = HashMap::new();
        for (id, module) in parsed {
            direct.insert(id.clone(), declared_symbols(&module.tops, id, true));
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
                            id.symbol_from_import_path(tree.path, graph)
                                .ok_or_else(|| {
                                    Diagnostic::new("pub use path must include a module and symbol")
                                })?;
                        let dep = id.resolve_import_module(tree.path, graph)?;
                        let dep_exports = exports.get(&dep).ok_or_else(|| {
                            Diagnostic::new(format!("module not found: {}", display_module(&dep)))
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
        graph: &PackageModuleGraph,
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
        for dep in import_deps(id, &module.tops, graph)? {
            let (_dep_root, dep_file) = module_file(root, &dep, graph)?;
            if !parsed.contains_key(&dep) || !dep_file.exists() {
                return Err(Diagnostic::new(format!(
                    "module not found: {} at {}",
                    display_module(&dep),
                    dep_file.display()
                )));
            }
            self.visit_module(&dep, root, graph, parsed, env, visiting, done)?;
        }
        visiting.pop();
        let rewritten = self.rewrite_module(module, &env.exports, graph)?;
        env.rewritten.insert(id.clone(), rewritten);
        env.order.push(id.clone());
        done.insert(id.clone());
        Ok(())
    }

    fn rewrite_module(
        &self,
        module: &ParsedModule<'bump>,
        exports: &HashMap<ModuleId, HashMap<String, String>>,
        graph: &PackageModuleGraph,
    ) -> Result<Vec<TopLevel<'bump>>, Diagnostic> {
        let mut imports = HashMap::new();
        for import in module_imports(&module.tops) {
            for tree in import.trees {
                let full = module
                    .id
                    .symbol_from_import_path(tree.path, graph)
                    .ok_or_else(|| Diagnostic::new("use path must include a module and symbol"))?;
                let dep = module.id.resolve_import_module(tree.path, graph)?;
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
        let own_names = declared_symbols(&module.tops, &module.id, false)
            .into_iter()
            .map(|(symbol, target)| {
                let local = symbol.rsplit("::").next().unwrap_or(&symbol).to_string();
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
            Term::Unsafe(inner) => self
                .arena
                .unsafe_(self.rewrite_module_term(inner, imports, own_names, scope)),
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
            return Err(Diagnostic::new("entry module must define `main : IO Unit`"));
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

fn import_deps<'bump>(
    current: &ModuleId,
    tops: &[TopLevel<'bump>],
    graph: &PackageModuleGraph,
) -> Result<Vec<ModuleId>, Diagnostic> {
    let mut deps = Vec::new();
    let mut seen = HashSet::new();
    for import in module_imports(tops) {
        for tree in import.trees {
            if tree.path.len() < 2 {
                return Err(Diagnostic::new("use path must include a module and symbol"));
            }
            let dep = current.resolve_import_module(tree.path, graph)?;
            if seen.insert(dep.clone()) {
                deps.push(dep);
            }
        }
    }
    Ok(deps)
}

fn declared_symbols<'bump>(
    tops: &[TopLevel<'bump>],
    module: &ModuleId,
    public_only: bool,
) -> HashMap<String, String> {
    tops.iter()
        .filter_map(|top| {
            let (top, public) = unwrap_public(top);
            if public_only && !public {
                return None;
            }
            match top {
                TopLevel::TLDef(name, ..) | TopLevel::TLTheorem(name, ..) => {
                    let symbol = module.join_symbol(name);
                    Some((symbol.clone(), symbol))
                }
                TopLevel::TLExternDef(name, ..) => {
                    Some((module.join_symbol(name), name.to_string()))
                }
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

fn module_file(
    root: &Path,
    module: &ModuleId,
    graph: &PackageModuleGraph,
) -> Result<(PathBuf, PathBuf), Diagnostic> {
    let module_root = if let Some(package) = &module.package {
        graph
            .packages
            .get(package)
            .map(|info| info.root.clone())
            .ok_or_else(|| {
                Diagnostic::new(format!("package dependency `{package}` was not resolved"))
            })?
    } else {
        root.to_path_buf()
    };
    let path = module_path(&module_root, module);
    Ok((module_root, path))
}

fn module_path(root: &Path, module: &ModuleId) -> PathBuf {
    let mut path = root.to_path_buf();
    for part in &module.path {
        path.push(part);
    }
    path.set_extension("lig");
    path
}

fn display_module(module: &ModuleId) -> String {
    let path = if module.path.is_empty() {
        "main".to_string()
    } else {
        module.path.join("::")
    };
    if let Some(package) = &module.package {
        format!("{package}::{path}")
    } else {
        path
    }
}
