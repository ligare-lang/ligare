use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::compiler::modules::{
    PackageModuleGraph, PackageModuleInfo, parse_module_surface, public_module_paths,
};
use crate::diagnostic::Diagnostic;

use super::git::{dep_cache_dir, ensure_git_checkout, git_commit, latest_git_tag};
use super::lock::{LockFile, LockedDependency, read_lock};
use super::manifest::{DepSource, Dependency, Manifest, read_manifest};

#[derive(Clone, Debug)]
pub struct ResolvedProject {
    pub root: PathBuf,
    pub manifest: Manifest,
    pub graph: PackageModuleGraph,
    pub lock: LockFile,
}

#[derive(Clone, Debug)]
pub enum UpdateMode {
    Locked,
    Latest,
    Version { name: String, version: String },
}

#[derive(Clone, Debug)]
struct ResolvedPackage {
    root: PathBuf,
    manifest: Manifest,
}

pub fn resolve_project(root: &Path, update: UpdateMode) -> Result<ResolvedProject, Diagnostic> {
    let manifest = read_manifest(root)?;
    let existing_lock = read_lock(root)?;
    let mut resolver = Resolver {
        update,
        root_lock: existing_lock,
        new_lock: LockFile::default(),
        packages: HashMap::new(),
        stack: Vec::new(),
    };
    resolver.resolve_manifest_deps(root, &manifest)?;
    let root_deps = manifest
        .dependencies
        .iter()
        .map(|dep| dep.name.clone())
        .collect::<HashSet<_>>();
    let packages = resolver
        .packages
        .into_iter()
        .map(|(name, package)| {
            let deps = package
                .manifest
                .dependencies
                .iter()
                .map(|dep| dep.name.clone())
                .collect::<HashSet<_>>();
            let root = module_root(&package.root, &package.manifest.entry);
            let entry = package.root.join(&package.manifest.entry);
            let mut public_modules =
                public_module_paths(&parse_module_surface(&package.root, &entry)?);
            public_modules.insert(vec!["main".to_string()]);
            let info = PackageModuleInfo {
                root,
                entry,
                deps,
                public_modules,
            };
            Ok((name, info))
        })
        .collect::<Result<HashMap<_, _>, Diagnostic>>()?;
    Ok(ResolvedProject {
        root: root.to_path_buf(),
        manifest,
        graph: PackageModuleGraph {
            root_deps,
            packages,
        },
        lock: resolver.new_lock,
    })
}

fn module_root(root: &Path, entry: &Path) -> PathBuf {
    root.join(entry)
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| root.to_path_buf())
}

struct Resolver {
    update: UpdateMode,
    root_lock: LockFile,
    new_lock: LockFile,
    packages: HashMap<String, ResolvedPackage>,
    stack: Vec<String>,
}

impl Resolver {
    fn resolve_manifest_deps(
        &mut self,
        package_root: &Path,
        manifest: &Manifest,
    ) -> Result<(), Diagnostic> {
        for dep in &manifest.dependencies {
            self.resolve_dep(package_root, dep)?;
        }
        Ok(())
    }

    fn resolve_dep(&mut self, package_root: &Path, dep: &Dependency) -> Result<(), Diagnostic> {
        if let Some(pos) = self.stack.iter().position(|name| name == &dep.name) {
            let mut cycle = self.stack[pos..].to_vec();
            cycle.push(dep.name.clone());
            return Err(Diagnostic::new(format!(
                "cyclic package dependency: {}",
                cycle.join(" -> ")
            )));
        }
        if self.packages.contains_key(&dep.name) {
            return Ok(());
        }
        self.stack.push(dep.name.clone());
        let resolved = self.resolve_dep_root(package_root, dep)?;
        let manifest = read_manifest(&resolved.root)?;
        if manifest.name != dep.name {
            return Err(Diagnostic::new(format!(
                "dependency `{}` manifest declares package `{}`",
                dep.name, manifest.name
            )));
        }
        for child in &manifest.dependencies {
            self.resolve_dep(&resolved.root, child)?;
        }
        self.new_lock
            .deps
            .insert(dep.name.clone(), resolved.locked.clone());
        self.packages.insert(
            dep.name.clone(),
            ResolvedPackage {
                root: resolved.root,
                manifest,
            },
        );
        self.stack.pop();
        Ok(())
    }

    fn resolve_dep_root(
        &self,
        package_root: &Path,
        dep: &Dependency,
    ) -> Result<ResolvedDepRoot, Diagnostic> {
        match &dep.source {
            DepSource::Path(path) => {
                let root = package_root.join(path);
                let commit = git_commit(&root).unwrap_or_else(|_| "local".to_string());
                let version = dep.version.clone().unwrap_or_else(|| "local".to_string());
                Ok(ResolvedDepRoot {
                    root: root.clone(),
                    locked: LockedDependency {
                        source: path.to_string_lossy().into_owned(),
                        version,
                        commit,
                        path: root,
                    },
                })
            }
            DepSource::Git(url) => {
                let version = self.selected_git_version(dep, url)?;
                let cache = dep_cache_dir(&dep.name, &version)?;
                ensure_git_checkout(url, &version, &cache)?;
                let commit = git_commit(&cache)?;
                Ok(ResolvedDepRoot {
                    root: cache.clone(),
                    locked: LockedDependency {
                        source: url.clone(),
                        version,
                        commit,
                        path: cache,
                    },
                })
            }
        }
    }

    fn selected_git_version(&self, dep: &Dependency, url: &str) -> Result<String, Diagnostic> {
        if let UpdateMode::Version { name, version } = &self.update
            && name == &dep.name
        {
            return Ok(version.clone());
        }
        if matches!(self.update, UpdateMode::Latest) {
            return latest_git_tag(url)
                .or_else(|_| {
                    dep.version
                        .clone()
                        .ok_or_else(|| Diagnostic::new("no version"))
                })
                .or_else(|_| Ok("HEAD".to_string()));
        }
        if let Some(locked) = self.root_lock.deps.get(&dep.name) {
            return Ok(locked.version.clone());
        }
        Ok(dep.version.clone().unwrap_or_else(|| "HEAD".to_string()))
    }
}

#[derive(Clone, Debug)]
struct ResolvedDepRoot {
    root: PathBuf,
    locked: LockedDependency,
}
