use std::collections::{HashMap, HashSet};
use std::ffi::OsStr;
use std::path::{Path, PathBuf};

use bumpalo::Bump;

use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Tactic, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::{TopLevel, UseTree, Visibility, parse_program};

use super::cache::{
    CachedFile, FALLBACK_ROOT_PACKAGE, PackageCompilerCache, now_ms, package_root_for_file,
    source_hash,
};
use super::{Compiler, read_source_file};

const STANDARD_LIBRARY_PACKAGE: &str = "std";
const STANDARD_LIBRARY_PATH_ENV: &str = "LIGARE_STD_PATH";
const DEFAULT_STANDARD_LIBRARY_PATH: &str = "/usr/lib/ligare/std";

#[derive(Clone, Debug, Default)]
pub struct PackageModuleGraph {
    pub root_deps: HashSet<String>,
    pub packages: HashMap<String, PackageModuleInfo>,
}

#[derive(Clone, Debug)]
pub struct PackageModuleInfo {
    pub root: PathBuf,
    pub entry: PathBuf,
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

    fn package(package: &str, path: Vec<String>) -> Self {
        Self {
            package: Some(package.to_string()),
            path,
        }
    }

    fn child(&self, name: &str) -> Self {
        let mut path = self.path.clone();
        path.push(name.to_string());
        Self {
            package: self.package.clone(),
            path,
        }
    }

    fn parent(&self) -> Option<Self> {
        if self.path.is_empty() {
            return None;
        }
        let mut path = self.path.clone();
        path.pop();
        Some(Self {
            package: self.package.clone(),
            path,
        })
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

    fn local_symbol_name(&self, symbol: &str) -> String {
        let mut parts = Vec::new();
        if let Some(package) = &self.package {
            parts.push(package.clone());
        }
        parts.extend(self.path.clone());
        if parts.is_empty() {
            return symbol.to_string();
        }
        let prefix = format!("{}::", parts.join("::"));
        symbol.strip_prefix(&prefix).unwrap_or(symbol).to_string()
    }

    fn local_import_path_parts(&self, path: &[&str]) -> Self {
        Self {
            package: self.package.clone(),
            path: path[..path.len().saturating_sub(1)]
                .iter()
                .map(|p| (*p).to_string())
                .collect(),
        }
    }

    fn local_module_path_parts(&self, path: &[&str]) -> Self {
        let mut module_path = self.path.clone();
        module_path.extend(path.iter().map(|p| (*p).to_string()));
        Self {
            package: self.package.clone(),
            path: module_path,
        }
    }

    fn symbol_from_import_path(
        &self,
        path: &[Name<'_>],
        graph: &PackageModuleGraph,
    ) -> Option<String> {
        let parts = path.iter().map(|p| *p).collect::<Vec<_>>();
        self.symbol_from_import_path_parts(&parts, graph)
    }

    fn symbol_from_import_path_parts(
        &self,
        path: &[&str],
        graph: &PackageModuleGraph,
    ) -> Option<String> {
        let item = path.last()?;
        let module = self.resolve_import_module_parts(path, graph).ok()?;
        Some(module.join_symbol(item))
    }

    fn import_symbol_or_namespace_symbol(
        &self,
        path: &[Name<'_>],
        graph: &PackageModuleGraph,
    ) -> Result<(Self, String), Diagnostic> {
        let parts = path.iter().map(|p| *p).collect::<Vec<_>>();
        if parts.len() >= 3 && is_namespace_segment(parts[parts.len() - 2]) {
            let dep = self.resolve_namespace_module_parts(&parts, 2, graph)?;
            let logical = format!("{}::{}", parts[parts.len() - 2], parts[parts.len() - 1]);
            return Ok((dep.clone(), dep.join_symbol(&logical)));
        }
        let dep = self.resolve_import_module(path, graph)?;
        let full = self
            .symbol_from_import_path(path, graph)
            .ok_or_else(|| Diagnostic::new("use path must include a module and symbol"))?;
        Ok((dep, full))
    }

    fn namespace_import_prefix(
        &self,
        path: &[Name<'_>],
        graph: &PackageModuleGraph,
    ) -> Result<(Self, String), Diagnostic> {
        if path.len() < 2 {
            return Err(Diagnostic::new(
                "namespace wildcard use path must include a module and namespace",
            ));
        }
        let parts = path.iter().map(|p| *p).collect::<Vec<_>>();
        let dep = self.resolve_namespace_module_parts(&parts, 1, graph)?;
        let namespace = parts
            .last()
            .ok_or_else(|| Diagnostic::new("namespace use path cannot be empty"))?;
        Ok((dep.clone(), dep.join_symbol(namespace)))
    }

    fn wildcard_module_import(
        &self,
        path: &[Name<'_>],
        graph: &PackageModuleGraph,
    ) -> Result<Self, Diagnostic> {
        let parts = path.iter().map(|p| *p).collect::<Vec<_>>();
        self.resolve_import_module_path_parts(&parts, graph)
    }

    fn try_namespace_import(
        &self,
        path: &[Name<'_>],
        graph: &PackageModuleGraph,
    ) -> Result<Option<(Self, String, String)>, Diagnostic> {
        if path.len() < 2 {
            return Ok(None);
        }
        let parts = path.iter().map(|p| *p).collect::<Vec<_>>();
        let Some(namespace) = parts.last() else {
            return Ok(None);
        };
        if !is_namespace_segment(namespace) {
            return Ok(None);
        }
        let dep = self.resolve_namespace_module_parts(&parts, 1, graph)?;
        Ok(Some((
            dep.clone(),
            dep.join_symbol(namespace),
            namespace.to_string(),
        )))
    }

    fn resolve_namespace_module_parts(
        &self,
        path: &[&str],
        namespace_suffix_len: usize,
        graph: &PackageModuleGraph,
    ) -> Result<Self, Diagnostic> {
        if path.len() <= namespace_suffix_len {
            return Err(Diagnostic::new("namespace use path must include a module"));
        }
        let module_parts = &path[..path.len() - namespace_suffix_len];
        let symbol = "__namespace__";
        let mut synthetic = module_parts.to_vec();
        synthetic.push(symbol);
        self.resolve_import_module_parts(&synthetic, graph)
    }

    fn resolve_import_module(
        &self,
        path: &[Name<'_>],
        graph: &PackageModuleGraph,
    ) -> Result<Self, Diagnostic> {
        let parts = path.iter().map(|p| *p).collect::<Vec<_>>();
        self.resolve_import_module_parts(&parts, graph)
    }

    fn resolve_import_module_parts(
        &self,
        path: &[&str],
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
        if first == STANDARD_LIBRARY_PACKAGE {
            if path.len() < 3 {
                return Err(Diagnostic::new(
                    "standard library use path must be `std::module::symbol`",
                ));
            }
            let module_path = path[1..path.len() - 1]
                .iter()
                .map(|p| (*p).to_string())
                .collect::<Vec<_>>();
            return Ok(Self::package(STANDARD_LIBRARY_PACKAGE, module_path));
        }
        Ok(self.local_import_path_parts(path))
    }

    fn resolve_import_module_path_parts(
        &self,
        path: &[&str],
        graph: &PackageModuleGraph,
    ) -> Result<Self, Diagnostic> {
        if path.is_empty() {
            return Err(Diagnostic::new("wildcard use path must include a module"));
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
            if path.len() < 2 {
                return Err(Diagnostic::new(
                    "package wildcard use path must be `package::module::*`",
                ));
            }
            let module_path = path[1..]
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
        if first == STANDARD_LIBRARY_PACKAGE {
            if path.len() < 2 {
                return Err(Diagnostic::new(
                    "standard library wildcard use path must be `std::module::*`",
                ));
            }
            let module_path = path[1..]
                .iter()
                .map(|p| (*p).to_string())
                .collect::<Vec<_>>();
            return Ok(Self::package(STANDARD_LIBRARY_PACKAGE, module_path));
        }
        Ok(self.local_module_path_parts(path))
    }
}

#[derive(Clone)]
struct ParsedModule<'bump> {
    id: ModuleId,
    file: PathBuf,
    source_hash: u64,
    imports: Vec<Vec<String>>,
    tops: Vec<TopLevel<'bump>>,
}

#[derive(Clone, Debug)]
struct ModuleCacheRecord {
    package: String,
    package_root: PathBuf,
    file: PathBuf,
    entry: CachedFile,
}

#[derive(Clone, Debug)]
pub struct ParsedModuleSurface {
    pub path: Vec<String>,
    pub public: bool,
    pub children: Vec<ParsedModuleSurface>,
}

pub fn parse_module_surface(
    root: &Path,
    entry_path: &Path,
) -> Result<Vec<ParsedModuleSurface>, Diagnostic> {
    let module_root = entry_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| root.to_path_buf());
    parse_module_surface_at(&module_root, entry_path, Vec::new())
}

struct ModuleEnv<'bump> {
    exports: HashMap<ModuleId, HashMap<String, String>>,
    rewritten: HashMap<ModuleId, Vec<TopLevel<'bump>>>,
    cache_records: HashMap<ModuleId, ModuleCacheRecord>,
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
        line.starts_with("use ")
            || line.starts_with("pub use ")
            || line.starts_with("mod ")
            || line.starts_with("pub mod ")
            || line.starts_with("namespace ")
            || line.starts_with("pub namespace ")
            || line.contains("::")
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
        self.validate_module_main()?;
        let cache_root =
            package_root_for_file(Path::new(file)).unwrap_or_else(|| PathBuf::from("."));
        let root_package = root_cache_package_name(&cache_root);
        save_module_cache_records(&cache_root, &root_package, env.cache_records.into_values())
    }

    pub(crate) fn collect_module_entry(&mut self, file: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        let env = self.load_module_graph(file)?;
        let mut checked_records = Vec::new();
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
            self.enum_types.extend(monomorphized.codegen.enum_types);
            self.struct_types.extend(monomorphized.codegen.struct_types);
            self.tops.extend(erased.tops);
            if let Some(record) = env.cache_records.get(&id) {
                checked_records.push(record.clone());
            }
        }
        self.validate_module_main()?;
        let cache_root =
            package_root_for_file(Path::new(file)).unwrap_or_else(|| PathBuf::from("."));
        let root_package = root_cache_package_name(&cache_root);
        save_module_cache_records(&cache_root, &root_package, checked_records)
    }

    pub fn process_project_entry(
        &mut self,
        root: &Path,
        entry: &Path,
        graph: PackageModuleGraph,
    ) -> Result<(), Diagnostic> {
        let env = self.load_project_module_graph(root, entry, graph, true)?;
        let mut checked_records = Vec::new();
        for id in env.order {
            let tops = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in tops {
                self.process_top_level(top)?;
            }
            if let Some(record) = env.cache_records.get(&id) {
                checked_records.push(record.clone());
            }
        }
        self.validate_module_main()?;
        let root_package = root_cache_package_name(root);
        save_module_cache_records(root, &root_package, checked_records)
    }

    pub fn collect_project_entry(
        &mut self,
        root: &Path,
        entry: &Path,
        graph: PackageModuleGraph,
    ) -> Result<(), Diagnostic> {
        self.quiet = true;
        let env = self.load_project_module_graph(root, entry, graph, true)?;
        let mut checked_records = Vec::new();
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
            self.enum_types.extend(monomorphized.codegen.enum_types);
            self.struct_types.extend(monomorphized.codegen.struct_types);
            self.tops.extend(erased.tops);
            if let Some(record) = env.cache_records.get(&id) {
                checked_records.push(record.clone());
            }
        }
        self.validate_module_main()?;
        let root_package = root_cache_package_name(root);
        save_module_cache_records(root, &root_package, checked_records)
    }

    pub fn collect_project_lib_entry(
        &mut self,
        root: &Path,
        entry: &Path,
        graph: PackageModuleGraph,
    ) -> Result<(), Diagnostic> {
        self.quiet = true;
        let env = self.load_project_module_graph(root, entry, graph, false)?;
        let mut checked_records = Vec::new();
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
            self.enum_types.extend(monomorphized.codegen.enum_types);
            self.struct_types.extend(monomorphized.codegen.struct_types);
            self.tops.extend(erased.tops);
            if let Some(record) = env.cache_records.get(&id) {
                checked_records.push(record.clone());
            }
        }
        let root_package = root_cache_package_name(root);
        save_module_cache_records(root, &root_package, checked_records)?;
        Ok(())
    }

    fn load_module_graph(&self, entry: &str) -> Result<ModuleEnv<'bump>, Diagnostic> {
        let entry_path = PathBuf::from(entry);
        let root = entry_path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from("."));
        self.load_project_module_graph(&root, &entry_path, PackageModuleGraph::default(), true)
    }

    fn load_project_module_graph(
        &self,
        root: &Path,
        entry_path: &Path,
        graph: PackageModuleGraph,
        require_main: bool,
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
        if require_main && entry_id == ModuleId::root() && !has_public_main(&root_module.tops) {
            return Err(Diagnostic::new(format!(
                "entry module `{}` must define `pub main : IO ()`",
                entry_path.display()
            )));
        }
        let exports = self.collect_exports(&parsed, &graph)?;
        let cache_records = module_cache_records(&parsed, &exports);
        let mut env = ModuleEnv {
            exports,
            rewritten: HashMap::new(),
            cache_records,
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
        let hash = source_hash(&source);
        let tops = parse_program(&source, self.bump, self.arena)
            .map_err(|e| Diagnostic::with_span(format!("parse error: {}", e.message), e.span))
            .map_err(|d| d.with_source(&file_str, &source))?;
        let imports = module_cache_imports(&id, &tops, graph)?;
        parsed.insert(
            id.clone(),
            ParsedModule {
                id: id.clone(),
                file: file.clone(),
                source_hash: hash,
                imports,
                tops: tops.clone(),
            },
        );
        for module in declared_module_deps(&id, &tops) {
            self.ensure_declared_module_loaded(root, &module, graph, parsed)?;
        }
        for module in import_deps(&id, &tops, graph)? {
            self.ensure_declared_module_loaded(root, &module, graph, parsed)?;
        }
        for module in qualified_term_deps(&id, &tops, graph)? {
            self.ensure_declared_module_loaded(root, &module, graph, parsed)?;
        }
        Ok(id)
    }

    fn ensure_declared_module_loaded(
        &self,
        root: &Path,
        module: &ModuleId,
        graph: &PackageModuleGraph,
        parsed: &mut HashMap<ModuleId, ParsedModule<'bump>>,
    ) -> Result<(), Diagnostic> {
        if parsed.contains_key(module) {
            return Ok(());
        }

        if is_standard_library_module(module, graph) && !module.path.is_empty() {
            let (module_root, file) = module_file(root, module, graph)?;
            self.load_module_as(&module_root, file, module.clone(), graph, parsed)?;
            return Ok(());
        }

        if module.path == ["main"] {
            let (module_root, file) = module_file(root, module, graph)?;
            self.load_module_as(&module_root, file, module.clone(), graph, parsed)?;
            return Ok(());
        }

        let Some(parent) = module.parent() else {
            let (module_root, file) = module_file(root, module, graph)?;
            self.load_module_as(&module_root, file, module.clone(), graph, parsed)?;
            return Ok(());
        };
        self.ensure_declared_module_loaded(root, &parent, graph, parsed)?;
        let leaf = module
            .path
            .last()
            .ok_or_else(|| Diagnostic::new("module path cannot be empty"))?;
        let parent_module = parsed.get(&parent).ok_or_else(|| {
            Diagnostic::new(format!("module not found: {}", display_module(&parent)))
        })?;
        if !declares_module(&parent_module.tops, leaf) {
            return Err(Diagnostic::new(format!(
                "module `{}` is not declared by parent module `{}`",
                display_module(module),
                display_module(&parent)
            )));
        }
        let (module_root, file) = module_file(root, module, graph)?;
        self.load_module_as(&module_root, file, module.clone(), graph, parsed)
            .map(|_| ())
    }

    fn collect_exports(
        &self,
        parsed: &HashMap<ModuleId, ParsedModule<'bump>>,
        graph: &PackageModuleGraph,
    ) -> Result<HashMap<ModuleId, HashMap<String, String>>, Diagnostic> {
        let mut direct = HashMap::new();
        for (id, module) in parsed {
            validate_namespace_conflicts(&module.tops)?;
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
                        if tree.wildcard {
                            let dep = if is_namespace_wildcard_path(tree.path) {
                                module.id.namespace_import_prefix(tree.path, graph)?.0
                            } else {
                                module.id.wildcard_module_import(tree.path, graph)?
                            };
                            let dep_exports = exports.get(&dep).ok_or_else(|| {
                                Diagnostic::new(format!(
                                    "module not found: {}",
                                    display_module(&dep)
                                ))
                            })?;
                            if is_namespace_wildcard_path(tree.path) {
                                let (_, prefix) =
                                    module.id.namespace_import_prefix(tree.path, graph)?;
                                let prefix_with_sep = format!("{prefix}::");
                                for (exported, target) in dep_exports {
                                    let Some(local) = exported.strip_prefix(&prefix_with_sep)
                                    else {
                                        continue;
                                    };
                                    if local.contains("::") {
                                        continue;
                                    }
                                    let exported = id.join_symbol(local);
                                    if set.insert(exported, target.clone()).is_none() {
                                        changed = true;
                                    }
                                }
                            } else {
                                for (exported, target) in dep_exports {
                                    let local = dep.local_symbol_name(exported);
                                    let exported = id.join_symbol(&local);
                                    if set.insert(exported, target.clone()).is_none() {
                                        changed = true;
                                    }
                                }
                            }
                            continue;
                        }
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
        for dep in declared_module_deps(id, &module.tops)
            .into_iter()
            .chain(import_deps(id, &module.tops, graph)?)
            .chain(qualified_term_deps(id, &module.tops, graph)?)
        {
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
                TopLevel::TLNamespace(name, items, span) => {
                    self.rewrite_namespace_items(
                        &module.id,
                        name,
                        items,
                        span.clone(),
                        &imports,
                        &own_names,
                        &mut out,
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
        _span: std::ops::Range<usize>,
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
            Term::Named(name) | Term::Builtin(name) | Term::Global(name) => {
                if scope.contains(name) {
                    return term;
                }
                if let Some(full) = imports.get(*name).or_else(|| own_names.get(*name)) {
                    return self.arena.named(self.arena.alloc_str(full));
                }
                term
            }
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

    fn validate_module_main(&self) -> Result<(), Diagnostic> {
        if !self.env.contains_key("main") {
            return Err(Diagnostic::new("entry module must define `main : IO ()`"));
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

fn insert_import(
    imports: &mut HashMap<String, String>,
    local: String,
    target: String,
) -> Result<(), Diagnostic> {
    if let Some(existing) = imports.get(&local)
        && existing != &target
    {
        return Err(Diagnostic::new(format!(
            "duplicate import `{local}` from `{existing}` and `{target}`"
        )));
    }
    imports.insert(local, target);
    Ok(())
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
            if tree.path.len() < 2 && !tree.wildcard {
                return Err(Diagnostic::new("use path must include a module and symbol"));
            }
            let dep = if tree.wildcard {
                if is_namespace_wildcard_path(tree.path) {
                    current.namespace_import_prefix(tree.path, graph)?.0
                } else {
                    current.wildcard_module_import(tree.path, graph)?
                }
            } else if tree.path.len() >= 3 && is_namespace_segment(tree.path[tree.path.len() - 2]) {
                let parts = tree.path.iter().map(|p| *p).collect::<Vec<_>>();
                current.resolve_namespace_module_parts(&parts, 2, graph)?
            } else if tree.path.len() >= 2 && is_namespace_segment(tree.path[tree.path.len() - 1]) {
                let parts = tree.path.iter().map(|p| *p).collect::<Vec<_>>();
                current.resolve_namespace_module_parts(&parts, 1, graph)?
            } else {
                current.resolve_import_module(tree.path, graph)?
            };
            if seen.insert(dep.clone()) {
                deps.push(dep);
            }
        }
    }
    Ok(deps)
}

fn module_cache_imports<'bump>(
    current: &ModuleId,
    tops: &[TopLevel<'bump>],
    graph: &PackageModuleGraph,
) -> Result<Vec<Vec<String>>, Diagnostic> {
    let mut deps = declared_module_deps(current, tops);
    deps.extend(import_deps(current, tops, graph)?);
    deps.extend(qualified_term_deps(current, tops, graph)?);
    let mut imports = deps
        .into_iter()
        .map(|dep| module_cache_path(&dep))
        .collect::<Vec<_>>();
    imports.sort();
    imports.dedup();
    Ok(imports)
}

fn module_cache_path(module: &ModuleId) -> Vec<String> {
    let mut path = Vec::new();
    if let Some(package) = &module.package {
        path.push(package.clone());
    }
    if module.path.is_empty() {
        path.push("main".to_string());
    } else {
        path.extend(module.path.clone());
    }
    path
}

fn module_cache_records<'bump>(
    parsed: &HashMap<ModuleId, ParsedModule<'bump>>,
    exports: &HashMap<ModuleId, HashMap<String, String>>,
) -> HashMap<ModuleId, ModuleCacheRecord> {
    parsed
        .iter()
        .map(|(id, module)| {
            let mut exported = exports
                .get(id)
                .map(|exports| {
                    exports
                        .keys()
                        .map(|symbol| id.local_symbol_name(symbol))
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            exported.sort();
            exported.dedup();
            (
                id.clone(),
                ModuleCacheRecord {
                    package: id
                        .package
                        .clone()
                        .unwrap_or_else(|| FALLBACK_ROOT_PACKAGE.to_string()),
                    package_root: package_root_for_file(&module.file).unwrap_or_else(|| {
                        module
                            .file
                            .parent()
                            .map(Path::to_path_buf)
                            .unwrap_or_else(|| PathBuf::from("."))
                    }),
                    file: module.file.clone(),
                    entry: CachedFile {
                        package: id.package.clone(),
                        module_path: id.path.clone(),
                        source_hash: module.source_hash,
                        imports: module.imports.clone(),
                        exports: exported,
                        checked_ok: true,
                        updated_at_ms: now_ms(),
                    },
                },
            )
        })
        .collect()
}

fn save_module_cache_records(
    target_root: &Path,
    root_package: &str,
    records: impl IntoIterator<Item = ModuleCacheRecord>,
) -> Result<(), Diagnostic> {
    let mut caches = HashMap::<(String, PathBuf), PackageCompilerCache>::new();
    for record in records {
        let package = if record.package == FALLBACK_ROOT_PACKAGE {
            root_package.to_string()
        } else {
            record.package.clone()
        };
        let key = (package.clone(), record.package_root.clone());
        caches
            .entry(key)
            .or_insert_with(|| {
                PackageCompilerCache::load(target_root, &record.package_root, &package)
            })
            .update(&record.file, record.entry);
    }
    for cache in caches.values() {
        cache.save()?;
    }
    Ok(())
}

fn root_cache_package_name(root: &Path) -> String {
    crate::package::read_manifest(root)
        .map(|manifest| manifest.name)
        .unwrap_or_else(|_| FALLBACK_ROOT_PACKAGE.to_string())
}

fn qualified_term_deps<'bump>(
    current: &ModuleId,
    tops: &[TopLevel<'bump>],
    graph: &PackageModuleGraph,
) -> Result<Vec<ModuleId>, Diagnostic> {
    let mut deps = Vec::new();
    let mut seen = HashSet::new();
    let namespace_aliases = namespace_aliases_in_uses(tops);
    for name in qualified_names_in_tops(tops) {
        let Some(parts) = qualified_symbol_parts(&name) else {
            continue;
        };
        if namespace_aliases.contains(parts[0]) {
            continue;
        }
        let dep = current.resolve_import_module_parts(&parts, graph)?;
        if seen.insert(dep.clone()) {
            deps.push(dep);
        }
    }
    Ok(deps)
}

fn qualified_term_names<'bump>(
    current: &ModuleId,
    tops: &[TopLevel<'bump>],
    graph: &PackageModuleGraph,
    exports: &HashMap<ModuleId, HashMap<String, String>>,
) -> Result<HashMap<String, String>, Diagnostic> {
    let mut resolved = HashMap::new();
    let namespace_aliases = namespace_aliases_in_uses(tops);
    for name in qualified_names_in_tops(tops) {
        let Some(parts) = qualified_symbol_parts(&name) else {
            continue;
        };
        if namespace_aliases.contains(parts[0]) {
            continue;
        }
        let requested = current
            .symbol_from_import_path_parts(&parts, graph)
            .ok_or_else(|| Diagnostic::new("qualified path must include a module and symbol"))?;
        let dep = current.resolve_import_module_parts(&parts, graph)?;
        let dep_exports = exports.get(&dep).ok_or_else(|| {
            Diagnostic::new(format!("module not found: {}", display_module(&dep)))
        })?;
        let Some(target) = dep_exports.get(&requested) else {
            return Err(Diagnostic::new(format!(
                "cannot reference private or unknown symbol `{requested}`"
            )));
        };
        resolved.insert(name, target.clone());
    }
    Ok(resolved)
}

fn namespace_aliases_in_uses<'bump>(tops: &[TopLevel<'bump>]) -> HashSet<String> {
    let mut aliases = HashSet::new();
    for import in module_imports(tops) {
        for tree in import.trees {
            if !tree.wildcard
                && tree.path.len() >= 2
                && is_namespace_segment(tree.path[tree.path.len() - 1])
            {
                aliases.insert(
                    tree.alias
                        .map(|alias| alias.to_string())
                        .unwrap_or_else(|| tree.path[tree.path.len() - 1].to_string()),
                );
            }
        }
    }
    aliases
}

fn qualified_symbol_parts(name: &str) -> Option<Vec<&str>> {
    if !name.contains("::") {
        return None;
    }
    let parts = name.split("::").collect::<Vec<_>>();
    if parts.len() < 2 || parts.iter().any(|part| part.is_empty()) {
        None
    } else {
        Some(parts)
    }
}

fn is_namespace_segment(name: &str) -> bool {
    name.chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_uppercase())
}

fn is_namespace_wildcard_path(path: &[Name<'_>]) -> bool {
    path.len() >= 2 && path.last().is_some_and(|name| is_namespace_segment(name))
}

fn qualified_names_in_tops<'bump>(tops: &[TopLevel<'bump>]) -> HashSet<String> {
    let mut names = HashSet::new();
    for top in tops {
        collect_qualified_names_from_top(top, &mut names);
    }
    names
}

fn collect_qualified_names_from_top<'bump>(top: &TopLevel<'bump>, names: &mut HashSet<String>) {
    let (top, _) = unwrap_public(top);
    match top {
        TopLevel::TLDef(_, params, ret, body, _) => {
            collect_qualified_names_from_params(params, names);
            if let Some(ret) = ret {
                collect_qualified_names_from_term(ret, names);
            }
            collect_qualified_names_from_term(body, names);
        }
        TopLevel::TLExternDef(_, params, ret, _) => {
            collect_qualified_names_from_params(params, names);
            collect_qualified_names_from_term(ret, names);
        }
        TopLevel::TLInstance(_, constraint, value, _) => {
            collect_qualified_names_from_term(constraint, names);
            collect_qualified_names_from_term(value, names);
        }
        TopLevel::TLVariable(params, _) => {
            collect_qualified_names_from_params(params, names);
        }
        TopLevel::TLTheorem(_, prop, body, _) | TopLevel::TLCheck(prop, body, _) => {
            collect_qualified_names_from_term(prop, names);
            collect_qualified_names_from_term(body, names);
        }
        TopLevel::TLEval(term, _) | TopLevel::TLExpr(term, _) | TopLevel::TLSplice(term, _) => {
            collect_qualified_names_from_term(term, names);
        }
        TopLevel::TLUse(..) | TopLevel::TLMod(..) | TopLevel::TLPublic(_) => {}
        TopLevel::TLAttributed(_, inner, _) => collect_qualified_names_from_top(inner, names),
        TopLevel::TLNamespace(_, items, _) => {
            for item in *items {
                collect_qualified_names_from_top(item, names);
            }
        }
    }
}

fn collect_qualified_names_from_params<'bump>(
    params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
    names: &mut HashSet<String>,
) {
    for (_, constraint) in params {
        if let Some(constraint) = constraint {
            collect_qualified_names_from_term(constraint, names);
        }
    }
}

fn collect_qualified_names_from_term<'bump>(term: &'bump Term<'bump>, names: &mut HashSet<String>) {
    match term {
        Term::Named(name) | Term::Global(name) => {
            if qualified_symbol_parts(name).is_some() {
                names.insert((*name).to_string());
            }
        }
        Term::App(f, a) => {
            collect_qualified_names_from_term(f, names);
            collect_qualified_names_from_term(a, names);
        }
        Term::Implicit(inner)
        | Term::Lam(inner)
        | Term::NamedLam(_, inner)
        | Term::Unsafe(inner)
        | Term::Pure(inner)
        | Term::Quote(inner)
        | Term::Splice(inner)
        | Term::StructProj(inner, _)
        | Term::MethodCall(inner, _) => collect_qualified_names_from_term(inner, names),
        Term::Pi(_, a, b) | Term::Refine(_, a, b) | Term::Annot(a, b) => {
            collect_qualified_names_from_term(a, names);
            collect_qualified_names_from_term(b, names);
        }
        Term::Let(_, val, body, constraint) => {
            collect_qualified_names_from_term(val, names);
            collect_qualified_names_from_term(body, names);
            if let Some(constraint) = constraint {
                collect_qualified_names_from_term(constraint, names);
            }
        }
        Term::IfThenElse(c, t, f) => {
            collect_qualified_names_from_term(c, names);
            collect_qualified_names_from_term(t, names);
            collect_qualified_names_from_term(f, names);
        }
        Term::ByProof(inner, tactics) => {
            if let Some(inner) = inner {
                collect_qualified_names_from_term(inner, names);
            }
            for tactic in tactics.iter() {
                match *tactic {
                    Tactic::Exact(term) | Tactic::Apply(term) | Tactic::Have(_, term) => {
                        collect_qualified_names_from_term(term, names);
                    }
                    Tactic::Intro(_) => {}
                    Tactic::Custom(_, args) => {
                        for arg in args {
                            collect_qualified_names_from_term(arg, names);
                        }
                    }
                }
            }
        }
        Term::EnumDef(_, variants) => {
            for (_, fields) in variants.iter() {
                for (_, constraint) in fields.iter() {
                    collect_qualified_names_from_term(constraint, names);
                }
            }
        }
        Term::Variant(_, _, values) | Term::StructCons(_, values) => {
            for value in values.iter() {
                collect_qualified_names_from_term(value, names);
            }
        }
        Term::Match(scrut, branches) => {
            collect_qualified_names_from_term(scrut, names);
            for (_, binds, body) in branches.iter() {
                for (_, constraint) in binds.iter() {
                    collect_qualified_names_from_term(constraint, names);
                }
                collect_qualified_names_from_term(body, names);
            }
        }
        Term::NamedMatch(scrut, branches) => {
            collect_qualified_names_from_term(scrut, names);
            for (_, binds, body) in branches.iter() {
                for (_, constraint) in binds.iter() {
                    collect_qualified_names_from_term(constraint, names);
                }
                collect_qualified_names_from_term(body, names);
            }
        }
        Term::Do(stmts) => {
            for stmt in stmts.iter() {
                match *stmt {
                    crate::core::syntax::DoStmt::Bind(_, rhs)
                    | crate::core::syntax::DoStmt::Expr(rhs) => {
                        collect_qualified_names_from_term(rhs, names);
                    }
                    crate::core::syntax::DoStmt::Let(_, rhs, constraint) => {
                        collect_qualified_names_from_term(rhs, names);
                        if let Some(constraint) = constraint {
                            collect_qualified_names_from_term(constraint, names);
                        }
                    }
                }
            }
        }
        Term::StructDef(_, fields) => {
            for (_, constraint) in fields.iter() {
                collect_qualified_names_from_term(constraint, names);
            }
        }
        Term::Var(_)
        | Term::LitInt(_)
        | Term::LitBool(_)
        | Term::LitStr(_)
        | Term::PrimOp(_)
        | Term::Universe(_)
        | Term::Builtin(_)
        | Term::AutoProof
        | Term::RefParam => {}
    }
}

fn declared_module_deps<'bump>(current: &ModuleId, tops: &[TopLevel<'bump>]) -> Vec<ModuleId> {
    let mut deps = Vec::new();
    let mut seen = HashSet::new();
    for top in tops {
        let (top, _) = unwrap_public(top);
        if let TopLevel::TLMod(name, _) = top {
            let dep = current.child(name);
            if seen.insert(dep.clone()) {
                deps.push(dep);
            }
        }
    }
    deps
}

fn declares_module<'bump>(tops: &[TopLevel<'bump>], name: &str) -> bool {
    tops.iter().any(|top| {
        let (top, _) = unwrap_public(top);
        matches!(top, TopLevel::TLMod(module_name, _) if *module_name == name)
    })
}

fn parse_module_surface_at(
    module_root: &Path,
    file: &Path,
    path: Vec<String>,
) -> Result<Vec<ParsedModuleSurface>, Diagnostic> {
    let file_str = file.to_string_lossy().into_owned();
    let source = read_source_file(&file_str)?;
    let bump = Bump::new();
    let arena = TermArena::new(&bump);
    let tops = parse_program(&source, &bump, &arena)
        .map_err(|e| Diagnostic::with_span(format!("parse error: {}", e.message), e.span))
        .map_err(|d| d.with_source(&file_str, &source))?;
    let mut surfaces = Vec::new();
    for top in &tops {
        let (top, public) = unwrap_public(top);
        let TopLevel::TLMod(name, _) = top else {
            continue;
        };
        let mut child_path = path.clone();
        child_path.push(name.to_string());
        let child_id = ModuleId {
            package: None,
            path: child_path.clone(),
        };
        let child_file = module_path(module_root, &child_id)?;
        if !child_file.exists() {
            return Err(Diagnostic::new(format!(
                "module not found: {} at {}",
                display_module(&child_id),
                child_file.display()
            )));
        }
        let children = parse_module_surface_at(module_root, &child_file, child_path.clone())?;
        surfaces.push(ParsedModuleSurface {
            path: child_path,
            public,
            children,
        });
    }
    Ok(surfaces)
}

pub fn public_module_paths(surface: &[ParsedModuleSurface]) -> HashSet<Vec<String>> {
    let mut paths = HashSet::new();
    for module in surface {
        collect_public_module_paths(module, true, &mut paths);
    }
    paths
}

fn collect_public_module_paths(
    module: &ParsedModuleSurface,
    parent_public: bool,
    paths: &mut HashSet<Vec<String>>,
) {
    let public = parent_public && module.public;
    if public {
        paths.insert(module.path.clone());
    }
    for child in &module.children {
        collect_public_module_paths(child, public, paths);
    }
}

fn declared_symbols<'bump>(
    tops: &[TopLevel<'bump>],
    module: &ModuleId,
    public_only: bool,
) -> HashMap<String, String> {
    let mut out = HashMap::new();
    collect_declared_symbols(tops, module, public_only, None, &mut out);
    out
}

fn validate_namespace_conflicts<'bump>(tops: &[TopLevel<'bump>]) -> Result<(), Diagnostic> {
    let mut seen: HashMap<(String, String, usize), std::ops::Range<usize>> = HashMap::new();
    for top in tops {
        let (top, _) = unwrap_public(top);
        let TopLevel::TLNamespace(namespace, items, _) = top else {
            continue;
        };
        for item in *items {
            let (item, public) = unwrap_public(item);
            if !public {
                continue;
            }
            if let TopLevel::TLDef(name, params, _, _, span)
            | TopLevel::TLExternDef(name, params, _, span) = item
            {
                let key = (namespace.to_string(), name.to_string(), params.len());
                if let Some(first) = seen.get(&key) {
                    return Err(Diagnostic::with_span(
                        format!(
                            "namespace `{}` has conflicting function `{}` with {} parameter(s); first declaration at {}..{}",
                            namespace,
                            name,
                            params.len(),
                            first.start,
                            first.end
                        ),
                        span.clone(),
                    ));
                }
                seen.insert(key, span.clone());
            }
        }
    }
    Ok(())
}

fn collect_declared_symbols<'bump>(
    tops: &[TopLevel<'bump>],
    module: &ModuleId,
    public_only: bool,
    namespace: Option<&str>,
    out: &mut HashMap<String, String>,
) {
    for top in tops {
        let (top, public) = unwrap_public(top);
        if public_only && !public {
            if !matches!(top, TopLevel::TLNamespace(..)) {
                continue;
            }
        }
        match top {
            TopLevel::TLDef(name, ..) | TopLevel::TLTheorem(name, ..) => {
                let logical = namespace
                    .map(|ns| format!("{ns}::{name}"))
                    .unwrap_or_else(|| name.to_string());
                let symbol = module.join_symbol(&logical);
                out.insert(symbol.clone(), symbol);
            }
            TopLevel::TLExternDef(name, ..) => {
                let logical = namespace
                    .map(|ns| format!("{ns}::{name}"))
                    .unwrap_or_else(|| name.to_string());
                let target = namespace
                    .map(|_| module.join_symbol(&logical))
                    .unwrap_or_else(|| name.to_string());
                out.insert(module.join_symbol(&logical), target);
            }
            TopLevel::TLNamespace(name, items, _) => {
                collect_declared_symbols(items, module, public_only, Some(name), out);
            }
            _ => {}
        }
    }
}

fn has_public_main<'bump>(tops: &[TopLevel<'bump>]) -> bool {
    tops.iter().any(|top| {
        let (top, public) = unwrap_public(top);
        public && matches!(top, TopLevel::TLDef(name, ..) if *name == "main")
    })
}

fn unwrap_public<'a, 'bump>(top: &'a TopLevel<'bump>) -> (&'a TopLevel<'bump>, bool) {
    let mut top = top;
    let mut public = false;
    loop {
        match top {
            TopLevel::TLPublic(inner) => {
                public = true;
                top = inner;
            }
            TopLevel::TLAttributed(_, inner, _) => top = inner,
            other => return (other, public),
        }
    }
}

fn module_file(
    root: &Path,
    module: &ModuleId,
    graph: &PackageModuleGraph,
) -> Result<(PathBuf, PathBuf), Diagnostic> {
    if is_standard_library_module(module, graph) {
        return standard_library_module_file(module);
    }
    let module_root = if let Some(package) = &module.package {
        let info = graph.packages.get(package).ok_or_else(|| {
            Diagnostic::new(format!("package dependency `{package}` was not resolved"))
        })?;
        if module.path.is_empty() {
            return Ok((info.root.clone(), info.entry.clone()));
        }
        info.root.clone()
    } else {
        root.to_path_buf()
    };
    let path = module_path(&module_root, module)?;
    Ok((module_root, path))
}

fn is_standard_library_module(module: &ModuleId, graph: &PackageModuleGraph) -> bool {
    module.package.as_deref() == Some(STANDARD_LIBRARY_PACKAGE)
        && !graph.packages.contains_key(STANDARD_LIBRARY_PACKAGE)
}

fn standard_library_module_file(module: &ModuleId) -> Result<(PathBuf, PathBuf), Diagnostic> {
    let configured_roots = standard_library_search_roots()?;
    let mut tried = Vec::new();
    for configured_root in &configured_roots {
        let module_root = standard_library_module_root(configured_root);
        let candidates = standard_library_module_candidates(&module_root, module);
        tried.extend(candidates.iter().cloned());
        match existing_module_candidate(module, &candidates)? {
            Some(path) => return Ok((module_root, path)),
            None => continue,
        }
    }
    Err(standard_library_not_found(
        module,
        &configured_roots,
        &tried,
    ))
}

fn standard_library_search_roots() -> Result<Vec<PathBuf>, Diagnostic> {
    standard_library_search_roots_from(std::env::var_os(STANDARD_LIBRARY_PATH_ENV).as_deref())
}

fn standard_library_search_roots_from(value: Option<&OsStr>) -> Result<Vec<PathBuf>, Diagnostic> {
    let roots = match value {
        Some(value) if !value.is_empty() => {
            let roots = std::env::split_paths(value)
                .filter(|path| !path.as_os_str().is_empty())
                .collect::<Vec<_>>();
            if roots.is_empty() {
                vec![PathBuf::from(DEFAULT_STANDARD_LIBRARY_PATH)]
            } else {
                roots
            }
        }
        _ => vec![PathBuf::from(DEFAULT_STANDARD_LIBRARY_PATH)],
    };
    for root in &roots {
        if root.is_relative() {
            return Err(Diagnostic::new(format!(
                "{STANDARD_LIBRARY_PATH_ENV} entries must be absolute paths: {}",
                root.display()
            )));
        }
    }
    Ok(roots)
}

fn standard_library_module_root(configured_root: &Path) -> PathBuf {
    let src = configured_root.join("src");
    if src.join("lib.lig").exists() {
        src
    } else {
        configured_root.to_path_buf()
    }
}

fn standard_library_module_candidates(root: &Path, module: &ModuleId) -> Vec<PathBuf> {
    if module.path.is_empty() {
        return vec![root.join("lib.lig"), root.join("mod.lig")];
    }
    let mut path = root.to_path_buf();
    for part in &module.path {
        path.push(part);
    }
    vec![path.with_extension("lig"), path.join("mod.lig")]
}

fn existing_module_candidate(
    module: &ModuleId,
    candidates: &[PathBuf],
) -> Result<Option<PathBuf>, Diagnostic> {
    let existing = candidates
        .iter()
        .filter(|path| path.exists())
        .cloned()
        .collect::<Vec<_>>();
    match existing.as_slice() {
        [] => Ok(None),
        [path] => Ok(Some(path.clone())),
        [file, folder_mod, ..] => Err(Diagnostic::new(format!(
            "ambiguous module `{}`: both `{}` and `{}` exist",
            display_module(module),
            file.display(),
            folder_mod.display()
        ))),
    }
}

fn standard_library_not_found(
    module: &ModuleId,
    roots: &[PathBuf],
    tried: &[PathBuf],
) -> Diagnostic {
    let roots = roots
        .iter()
        .map(|path| format!("  {}", path.display()))
        .collect::<Vec<_>>()
        .join("\n");
    let tried = tried
        .iter()
        .map(|path| format!("  {}", path.display()))
        .collect::<Vec<_>>()
        .join("\n");
    Diagnostic::new(format!(
        "standard library module `{}` not found\nsearched roots:\n{}\ntried:\n{}",
        display_module(module),
        roots,
        tried
    ))
}

fn module_path(root: &Path, module: &ModuleId) -> Result<PathBuf, Diagnostic> {
    if module.path.is_empty() {
        return Ok(root.join("main.lig"));
    }
    let mut path = root.to_path_buf();
    for part in &module.path {
        path.push(part);
    }
    let file = path.with_extension("lig");
    let folder_mod = path.join("mod.lig");
    match (file.exists(), folder_mod.exists()) {
        (true, false) => Ok(file),
        (false, true) => Ok(folder_mod),
        (true, true) => Err(Diagnostic::new(format!(
            "ambiguous module `{}`: both `{}` and `{}` exist",
            display_module(module),
            file.display(),
            folder_mod.display()
        ))),
        (false, false) => Ok(file),
    }
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

#[cfg(test)]
mod tests {
    use super::{DEFAULT_STANDARD_LIBRARY_PATH, standard_library_search_roots_from};
    use std::ffi::OsString;
    use std::path::PathBuf;

    #[test]
    fn unset_standard_library_path_uses_default_root() {
        assert_eq!(
            standard_library_search_roots_from(None).unwrap(),
            vec![PathBuf::from(DEFAULT_STANDARD_LIBRARY_PATH)]
        );
    }

    #[test]
    fn standard_library_path_splits_multiple_roots() {
        let joined = std::env::join_paths([PathBuf::from("/first"), PathBuf::from("/second")])
            .unwrap_or_else(|_| OsString::from("/first:/second"));
        assert_eq!(
            standard_library_search_roots_from(Some(&joined)).unwrap(),
            vec![PathBuf::from("/first"), PathBuf::from("/second")]
        );
    }

    #[test]
    fn relative_standard_library_path_is_rejected() {
        let err = standard_library_search_roots_from(Some(OsString::from("libs/std").as_os_str()))
            .unwrap_err();

        assert!(
            err.message
                .contains("LIGARE_STD_PATH entries must be absolute paths"),
            "{}",
            err.message
        );
    }
}
