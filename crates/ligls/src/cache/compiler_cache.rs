use super::*;

pub(super) fn resolve_module_imports(
    imports: &[Vec<String>],
    current_module: &ModuleKey,
    files: &HashMap<lsp::Url, FileCache>,
    project: Option<&ProjectContext>,
) -> HashSet<lsp::Url> {
    let module_index = files
        .iter()
        .map(|(uri, file)| (file.module_key.clone(), uri.clone()))
        .collect::<Vec<_>>();
    let source_uri = lsp::Url::parse("file:///.lig").expect("valid placeholder uri");
    resolve_module_imports_from_index(imports, current_module, &module_index, &source_uri, project)
}

pub(super) fn resolve_module_imports_from_index(
    imports: &[Vec<String>],
    current_module: &ModuleKey,
    module_index: &[(ModuleKey, lsp::Url)],
    source_uri: &lsp::Url,
    project: Option<&ProjectContext>,
) -> HashSet<lsp::Url> {
    imports
        .iter()
        .flat_map(|path| {
            project
                .map(|project| project.imported_module_keys(current_module, path))
                .unwrap_or_else(|| fallback_imported_module_keys(current_module, path))
        })
        .filter_map(|module| {
            module_index
                .iter()
                .find(|(module_key, uri)| module_key == &module && uri != source_uri)
                .map(|(_, uri)| uri.clone())
        })
        .collect()
}

pub(super) fn compiler_cache_is_fresh(
    uri: &lsp::Url,
    text_hash: u64,
    project: Option<&ProjectContext>,
    module: &ModuleKey,
) -> bool {
    let Ok(path) = uri.to_file_path() else {
        return false;
    };
    let Some(package_root) = package_root_for_file(&path) else {
        return false;
    };
    let target_root = project
        .map(ProjectContext::cache_target_root)
        .unwrap_or(package_root.as_path());
    let package = project
        .map(|project| project.cache_package_name(module))
        .unwrap_or_else(|| fallback_cache_package_name(module, &package_root));
    PackageCompilerCache::load(target_root, &package_root, &package).is_fresh(&path, text_hash)
}

pub(super) fn update_compiler_cache(
    uri: &lsp::Url,
    text_hash: u64,
    module: &ModuleKey,
    imports: &[Vec<String>],
    exports: &[String],
    checked_ok: bool,
    project: Option<&ProjectContext>,
) {
    let Ok(path) = uri.to_file_path() else {
        return;
    };
    let Some(package_root) = package_root_for_file(&path) else {
        return;
    };
    let target_root = project
        .map(ProjectContext::cache_target_root)
        .unwrap_or(package_root.as_path());
    let package = project
        .map(|project| project.cache_package_name(module))
        .unwrap_or_else(|| fallback_cache_package_name(module, &package_root));
    let mut cache = PackageCompilerCache::load(target_root, &package_root, &package);
    let mut imports = imports.to_vec();
    imports.sort();
    imports.dedup();
    let mut exports = exports.to_vec();
    exports.sort();
    exports.dedup();
    cache.update(
        &path,
        CachedFile {
            package: module.package.clone(),
            module_path: module.path.clone(),
            source_hash: text_hash,
            imports,
            exports,
            checked_ok,
            updated_at_ms: now_ms(),
        },
    );
    let _ = cache.save();
}

fn fallback_cache_package_name(module: &ModuleKey, package_root: &std::path::Path) -> String {
    module.package.clone().unwrap_or_else(|| {
        ligare::package::read_manifest(package_root)
            .map(|manifest| manifest.name)
            .unwrap_or_else(|_| FALLBACK_ROOT_PACKAGE.to_string())
    })
}
