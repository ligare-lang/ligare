use super::*;

pub(super) fn module_cache_imports<'bump>(
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

pub(super) fn module_cache_records<'bump>(
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

pub(super) fn save_module_cache_records(
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

pub(super) fn root_cache_package_name(root: &Path) -> String {
    crate::package::read_manifest(root)
        .map(|manifest| manifest.name)
        .unwrap_or_else(|_| FALLBACK_ROOT_PACKAGE.to_string())
}
