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

mod cache_io;
mod imports;
mod loader;
mod rewrite;
mod stdlib;
mod surface;

pub use self::surface::{parse_module_surface, public_module_paths};

use self::cache_io::{
    module_cache_imports, module_cache_records, root_cache_package_name, save_module_cache_records,
};
use self::imports::{
    declared_module_deps, declared_symbols, declares_module, has_public_main, import_deps,
    insert_import, is_namespace_segment, is_namespace_wildcard_path, module_imports,
    qualified_term_deps, qualified_term_names, unwrap_public, validate_namespace_conflicts,
};
use self::stdlib::{
    display_module, is_standard_library_module, module_file, module_path,
    should_auto_import_std_prelude, standard_prelude_module,
};

const STANDARD_LIBRARY_PACKAGE: &str = "std";
const STANDARD_PRELUDE_MODULE: &str = "prelude";
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
        let parts = path.to_vec();
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
        let parts = path.to_vec();
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
        let parts = path.to_vec();
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
        let parts = path.to_vec();
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
        let parts = path.to_vec();
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
        let parts = path.to_vec();
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

struct ModuleEnv<'bump> {
    exports: HashMap<ModuleId, HashMap<String, String>>,
    rewritten: HashMap<ModuleId, Vec<TopLevel<'bump>>>,
    cache_records: HashMap<ModuleId, ModuleCacheRecord>,
    order: Vec<ModuleId>,
}

struct ModuleVisitContext<'a, 'bump> {
    root: &'a Path,
    graph: &'a PackageModuleGraph,
    parsed: &'a HashMap<ModuleId, ParsedModule<'bump>>,
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

struct ImportItem<'a, 'bump> {
    trees: &'a [UseTree<'bump>],
    visibility: Visibility,
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
