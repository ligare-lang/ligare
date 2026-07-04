use super::*;

pub(super) fn module_file(
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

pub(super) fn is_standard_library_module(module: &ModuleId, graph: &PackageModuleGraph) -> bool {
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

pub(super) fn module_path(root: &Path, module: &ModuleId) -> Result<PathBuf, Diagnostic> {
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

pub(super) fn display_module(module: &ModuleId) -> String {
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

pub(super) fn standard_prelude_module() -> ModuleId {
    ModuleId::package(
        STANDARD_LIBRARY_PACKAGE,
        vec![STANDARD_PRELUDE_MODULE.to_string()],
    )
}

pub(super) fn should_auto_import_std_prelude(
    module: &ModuleId,
    graph: &PackageModuleGraph,
) -> bool {
    module.package.as_deref() != Some(STANDARD_LIBRARY_PACKAGE) && standard_prelude_available(graph)
}

fn standard_prelude_available(graph: &PackageModuleGraph) -> bool {
    if let Some(info) = graph.packages.get(STANDARD_LIBRARY_PACKAGE) {
        return info
            .public_modules
            .contains(&vec![STANDARD_PRELUDE_MODULE.to_string()]);
    }
    standard_library_module_file(&standard_prelude_module()).is_ok()
}
