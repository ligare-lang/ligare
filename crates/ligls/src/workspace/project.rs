use std::ffi::OsStr;
use std::path::{Component, Path, PathBuf};

use ligare::compiler::modules::{PackageModuleGraph, PackageModuleInfo};
use ligare::package::{UpdateMode, find_manifest_root, resolve_project};
use tower_lsp::lsp_types as lsp;

const STANDARD_LIBRARY_PACKAGE: &str = "std";
const STANDARD_LIBRARY_PATH_ENV: &str = "LIGARE_STD_PATH";
const DEFAULT_STANDARD_LIBRARY_PATH: &str = "/usr/lib/ligare/std";

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ModuleKey {
    pub(crate) package: Option<String>,
    pub(crate) path: Vec<String>,
}

impl ModuleKey {
    pub(crate) fn root() -> Self {
        Self {
            package: None,
            path: Vec::new(),
        }
    }

    fn package(package: impl Into<String>, path: Vec<String>) -> Self {
        Self {
            package: Some(package.into()),
            path,
        }
    }

    pub(crate) fn child(&self, name: impl Into<String>) -> Self {
        let mut path = self.path.clone();
        path.push(name.into());
        Self {
            package: self.package.clone(),
            path,
        }
    }

    pub(crate) fn join_symbol(&self, name: &str) -> String {
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
}

#[derive(Debug, Clone)]
pub(crate) struct ProjectContext {
    root: PathBuf,
    package_name: String,
    entry: PathBuf,
    module_root: PathBuf,
    graph: PackageModuleGraph,
    std_roots: Vec<PathBuf>,
}

impl ProjectContext {
    pub(crate) fn for_uri(uri: &lsp::Url) -> Option<Self> {
        let path = uri.to_file_path().ok()?;
        let root = find_manifest_root(&path).ok()?;
        let project = resolve_project(&root, UpdateMode::Locked).ok()?;
        let entry = root.join(&project.manifest.entry);
        let module_root = entry
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| root.clone());
        Some(Self {
            root,
            package_name: project.manifest.name,
            entry,
            module_root,
            graph: project.graph,
            std_roots: standard_library_module_roots(),
        })
    }

    pub(crate) fn module_key_for_uri(&self, uri: &lsp::Url) -> ModuleKey {
        let Ok(path) = uri.to_file_path() else {
            return ModuleKey::root();
        };
        if let Some(path) = normalize_existing_path(&path) {
            if same_path(&path, &self.entry) {
                return ModuleKey::root();
            }
            if let Some(module_path) = module_path_under_root(&path, &self.module_root, None) {
                return ModuleKey {
                    package: None,
                    path: module_path,
                };
            }
            for (name, info) in &self.graph.packages {
                if same_path(&path, &info.entry) {
                    return ModuleKey::package(name.clone(), package_entry_module_path(&path));
                }
                if let Some(module_path) = module_path_under_root(&path, &info.root, Some(info)) {
                    return ModuleKey::package(name.clone(), module_path);
                }
            }
            for std_root in &self.std_roots {
                if let Some(module_path) = module_path_under_root(&path, std_root, None) {
                    return ModuleKey::package(STANDARD_LIBRARY_PACKAGE, module_path);
                }
            }
        }
        fallback_module_key(uri)
    }

    pub(crate) fn cache_target_root(&self) -> &Path {
        &self.root
    }

    pub(crate) fn cache_package_name(&self, module: &ModuleKey) -> String {
        module
            .package
            .clone()
            .unwrap_or_else(|| self.package_name.clone())
    }

    pub(crate) fn imported_module_keys(
        &self,
        current: &ModuleKey,
        path: &[String],
    ) -> Vec<ModuleKey> {
        if path.is_empty() {
            return Vec::new();
        }
        let first = &path[0];
        if self.package_accessible_from(current, first) && path.len() >= 2 {
            let module_path = path[1..].to_vec();
            if self.package_exports(first, &module_path) {
                return vec![ModuleKey::package(first.clone(), module_path)];
            }
        }
        if first == STANDARD_LIBRARY_PACKAGE && path.len() >= 2 {
            return vec![ModuleKey::package(first.clone(), path[1..].to_vec())];
        }

        let mut candidates = vec![ModuleKey {
            package: current.package.clone(),
            path: path.to_vec(),
        }];
        if !current.path.is_empty() {
            let mut relative = current.path.clone();
            relative.extend(path.iter().cloned());
            candidates.push(ModuleKey {
                package: current.package.clone(),
                path: relative,
            });
        }
        candidates
    }

    pub(crate) fn file_candidates(&self, module: &ModuleKey) -> Vec<PathBuf> {
        match module.package.as_deref() {
            None if module.path.is_empty() => vec![self.entry.clone()],
            None => module_file_candidates(&self.module_root, &module.path),
            Some(STANDARD_LIBRARY_PACKAGE)
                if !self.graph.packages.contains_key(STANDARD_LIBRARY_PACKAGE) =>
            {
                self.std_roots
                    .iter()
                    .flat_map(|root| module_file_candidates(root, &module.path))
                    .collect()
            }
            Some(package) => {
                let Some(info) = self.graph.packages.get(package) else {
                    return Vec::new();
                };
                if module.path.is_empty() {
                    vec![info.entry.clone()]
                } else {
                    module_file_candidates(&info.root, &module.path)
                }
            }
        }
    }

    pub(crate) fn completion_module_paths(&self, current: &ModuleKey) -> Vec<Vec<String>> {
        let deps = match current.package.as_deref() {
            None => &self.graph.root_deps,
            Some(package) => {
                let Some(info) = self.graph.packages.get(package) else {
                    return Vec::new();
                };
                &info.deps
            }
        };
        let mut paths = Vec::new();
        for dep in deps {
            let Some(info) = self.graph.packages.get(dep) else {
                continue;
            };
            for module in &info.public_modules {
                let mut path = vec![dep.clone()];
                path.extend(module.iter().cloned());
                paths.push(path);
            }
        }
        if !self.graph.packages.contains_key(STANDARD_LIBRARY_PACKAGE) {
            paths.extend(standard_library_public_module_paths(&self.std_roots));
        }
        paths.sort();
        paths.dedup();
        paths
    }

    fn package_accessible_from(&self, current: &ModuleKey, package: &str) -> bool {
        match current.package.as_deref() {
            None => self.graph.root_deps.contains(package),
            Some(current_package) => self
                .graph
                .packages
                .get(current_package)
                .is_some_and(|info| info.deps.contains(package)),
        }
    }

    fn package_exports(&self, package: &str, module_path: &[String]) -> bool {
        self.graph
            .packages
            .get(package)
            .is_some_and(|info| info.public_modules.contains(module_path))
    }
}

pub(crate) fn project_context_for_uri(uri: &lsp::Url) -> Option<ProjectContext> {
    ProjectContext::for_uri(uri)
}

pub(crate) fn workspace_root_for_uris<'a>(
    uris: impl Iterator<Item = &'a lsp::Url>,
) -> Option<PathBuf> {
    let mut roots = uris
        .filter_map(|uri| uri.to_file_path().ok())
        .filter_map(|path| path.parent().map(Path::to_path_buf));
    let mut root = roots.next()?;
    for dir in roots {
        while !dir.starts_with(&root) {
            if !root.pop() {
                return None;
            }
        }
    }
    Some(root)
}

pub(crate) fn fallback_module_key(uri: &lsp::Url) -> ModuleKey {
    let root = workspace_root_for_uris(std::iter::once(uri));
    ModuleKey {
        package: None,
        path: fallback_module_path_for_uri(uri, root.as_deref()),
    }
}

pub(crate) fn fallback_imported_module_keys(
    current: &ModuleKey,
    path: &[String],
) -> Vec<ModuleKey> {
    if path.is_empty() {
        return Vec::new();
    }
    let mut candidates = vec![ModuleKey {
        package: current.package.clone(),
        path: path.to_vec(),
    }];
    if !current.path.is_empty() {
        let mut relative = current.path.clone();
        relative.extend(path.iter().cloned());
        candidates.push(ModuleKey {
            package: current.package.clone(),
            path: relative,
        });
    }
    candidates
}

pub(crate) fn fallback_file_candidates(root: &Path, module: &ModuleKey) -> Vec<PathBuf> {
    module_file_candidates(root, &module.path)
}

fn module_file_candidates(root: &Path, module: &[String]) -> Vec<PathBuf> {
    if module.is_empty() {
        return vec![root.join("main.lig"), root.join("lib.lig")];
    }
    let mut file = root.to_path_buf();
    for part in module {
        file.push(part);
    }
    let mut flat = file.clone();
    flat.set_extension("lig");
    vec![flat, file.join("mod.lig")]
}

fn fallback_module_path_for_uri(uri: &lsp::Url, root: Option<&Path>) -> Vec<String> {
    let Ok(path) = uri.to_file_path() else {
        return Vec::new();
    };
    let rel = root
        .and_then(|root| path.strip_prefix(root).ok())
        .unwrap_or(&path);
    module_path_from_relative(rel, None)
}

fn module_path_under_root(
    path: &Path,
    root: &Path,
    package: Option<&PackageModuleInfo>,
) -> Option<Vec<String>> {
    if let Some(info) = package
        && same_path(path, &info.entry)
    {
        return Some(package_entry_module_path(path));
    }
    let rel = path.strip_prefix(root).ok()?;
    Some(module_path_from_relative(
        rel,
        package.map(|info| &info.entry),
    ))
}

fn module_path_from_relative(rel: &Path, entry: Option<&PathBuf>) -> Vec<String> {
    let mut parts: Vec<String> = rel
        .components()
        .filter_map(|component| match component {
            Component::Normal(value) => value.to_str().map(str::to_string),
            _ => None,
        })
        .collect();
    let Some(file) = parts.pop() else {
        return Vec::new();
    };
    match file.as_str() {
        "main.lig" if entry.is_none() => Vec::new(),
        "lib.lig" if entry.is_none() => Vec::new(),
        "mod.lig" => parts,
        _ => {
            if let Some(stem) = file.strip_suffix(".lig") {
                parts.push(stem.to_string());
            }
            parts
        }
    }
}

fn package_entry_module_path(path: &Path) -> Vec<String> {
    match path.file_stem().and_then(|stem| stem.to_str()) {
        Some("main") => vec!["main".to_string()],
        Some("lib") => vec!["main".to_string()],
        Some(stem) => vec![stem.to_string()],
        None => Vec::new(),
    }
}

fn standard_library_module_roots() -> Vec<PathBuf> {
    standard_library_search_roots()
        .into_iter()
        .map(|root| {
            let src = root.join("src");
            if src.join("lib.lig").exists() {
                src
            } else {
                root
            }
        })
        .collect()
}

fn standard_library_public_module_paths(roots: &[PathBuf]) -> Vec<Vec<String>> {
    roots
        .iter()
        .flat_map(|root| {
            let lib = root.join("lib.lig");
            let Ok(source) = std::fs::read_to_string(lib) else {
                return Vec::new();
            };
            source
                .lines()
                .filter_map(|line| {
                    let line = line.trim_start();
                    let name = line.strip_prefix("pub mod ")?;
                    let name = name
                        .split(|ch: char| ch.is_whitespace() || ch == '-' || ch == '{')
                        .next()
                        .unwrap_or_default();
                    (!name.is_empty())
                        .then(|| vec![STANDARD_LIBRARY_PACKAGE.to_string(), name.to_string()])
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn standard_library_search_roots() -> Vec<PathBuf> {
    standard_library_search_roots_from(std::env::var_os(STANDARD_LIBRARY_PATH_ENV).as_deref())
}

fn standard_library_search_roots_from(value: Option<&OsStr>) -> Vec<PathBuf> {
    match value {
        Some(value) if !value.is_empty() => std::env::split_paths(value)
            .filter(|path| path.is_absolute())
            .filter(|path| !path.as_os_str().is_empty())
            .collect::<Vec<_>>(),
        _ => vec![PathBuf::from(DEFAULT_STANDARD_LIBRARY_PATH)],
    }
}

fn normalize_existing_path(path: &Path) -> Option<PathBuf> {
    path.canonicalize()
        .ok()
        .or_else(|| Some(path.to_path_buf()))
}

fn same_path(left: &Path, right: &Path) -> bool {
    let left = normalize_existing_path(left).unwrap_or_else(|| left.to_path_buf());
    let right = normalize_existing_path(right).unwrap_or_else(|| right.to_path_buf());
    left == right
}

#[cfg(test)]
mod tests {
    use super::standard_library_search_roots_from;
    use std::ffi::OsString;
    use std::path::PathBuf;

    #[test]
    fn relative_standard_library_path_is_not_used() {
        let roots =
            standard_library_search_roots_from(Some(OsString::from("libs/std").as_os_str()));

        assert!(roots.is_empty());
    }

    #[test]
    fn absolute_standard_library_path_is_used() {
        let roots =
            standard_library_search_roots_from(Some(OsString::from("/repo/libs/std").as_os_str()));

        assert_eq!(roots, vec![PathBuf::from("/repo/libs/std")]);
    }
}
