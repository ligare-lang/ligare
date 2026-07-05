use super::*;

pub(super) struct DirtyCheckContext<'a> {
    pub(super) uri: &'a lsp::Url,
    pub(super) text: &'a str,
    pub(super) dirty: &'a HashSet<usize>,
    pub(super) check: DiagnosticCheck,
    pub(super) files: &'a HashMap<lsp::Url, FileCache>,
    pub(super) project: Option<&'a ProjectContext>,
    pub(super) module_key: &'a ModuleKey,
}

pub(super) fn check_dirty_items<'bump>(
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
    ctx: DirtyCheckContext<'_>,
) -> HashMap<usize, Vec<lsp::Diagnostic>> {
    let mut compiler = Compiler::new(bump, arena);
    let module_index = ctx
        .files
        .iter()
        .map(|(uri, file)| (file.module_key.clone(), uri.clone()))
        .collect::<Vec<_>>();
    let mut work = Vec::new();

    for dep_uri in dependency_check_order(
        &module_imports_from_ranges(top_ranges),
        ctx.module_key,
        ctx.files,
        &module_index,
        ctx.uri,
        ctx.project,
    ) {
        let Some(file) = ctx.files.get(&dep_uri) else {
            continue;
        };
        let (dep_ast, _) = parse_program_lsp(&file.text, bump, arena);
        let dep_ranges = top_level_ranges(&file.text, &dep_ast);
        let dep_imports = imported_symbol_aliases(
            &file.module_key,
            &dep_ranges,
            ctx.files,
            &module_index,
            &dep_uri,
            ctx.project,
        );
        let dep_own =
            declared_symbol_aliases(dep_ranges.iter().map(|(_, _, top)| top), &file.module_key);
        for (_, _, top) in &dep_ranges {
            for top in rewrite_top_for_module(arena, top, &dep_imports, &dep_own) {
                work.push((usize::MAX, top, false));
            }
        }
    }

    let imports = imported_symbol_aliases(
        ctx.module_key,
        top_ranges,
        ctx.files,
        &module_index,
        ctx.uri,
        ctx.project,
    );
    let own = declared_symbol_aliases(top_ranges.iter().map(|(_, _, top)| top), ctx.module_key);
    work.extend(
        top_ranges
            .iter()
            .enumerate()
            .flat_map(|(idx, (_, _, top))| {
                rewrite_top_for_module(arena, top, &imports, &own)
                    .into_iter()
                    .map(move |top| (idx, top, ctx.dirty.contains(&idx)))
            }),
    );

    let diagnostics = compiler.check_top_levels_incremental_for_diagnostics(
        work,
        "<lsp>",
        ctx.text,
        CheckMode::from(ctx.check),
    );
    let mut by_item = HashMap::<usize, Vec<lsp::Diagnostic>>::new();
    for (idx, diagnostic) in diagnostics {
        if idx == usize::MAX {
            continue;
        }
        by_item
            .entry(idx)
            .or_default()
            .push(compiler_diagnostic_to_lsp(ctx.text, diagnostic));
    }
    let module_diagnostics = ModuleDiagnosticContext {
        current_module: ctx.module_key,
        files: ctx.files,
        module_index: &module_index,
        uri: ctx.uri,
        project: ctx.project,
    };
    for (idx, diagnostic) in
        use_module_diagnostics(ctx.text, top_ranges, ctx.dirty, &module_diagnostics)
    {
        by_item.entry(idx).or_default().push(diagnostic);
    }
    by_item
}

fn dependency_check_order(
    imports: &[Vec<String>],
    current_module: &ModuleKey,
    files: &HashMap<lsp::Url, FileCache>,
    module_index: &[(ModuleKey, lsp::Url)],
    source_uri: &lsp::Url,
    project: Option<&ProjectContext>,
) -> Vec<lsp::Url> {
    struct DepVisitContext<'a> {
        files: &'a HashMap<lsp::Url, FileCache>,
        module_index: &'a [(ModuleKey, lsp::Url)],
        source_uri: &'a lsp::Url,
        project: Option<&'a ProjectContext>,
    }

    fn visit(
        imports: &[Vec<String>],
        current_module: &ModuleKey,
        ctx: &DepVisitContext<'_>,
        seen: &mut HashSet<lsp::Url>,
        out: &mut Vec<lsp::Url>,
    ) {
        for module in imports.iter().flat_map(|path| {
            ctx.project
                .map(|project| project.imported_module_keys(current_module, path))
                .unwrap_or_else(|| fallback_imported_module_keys(current_module, path))
        }) {
            let Some(dep_uri) = ctx
                .module_index
                .iter()
                .find(|(module_key, uri)| module_key == &module && uri != ctx.source_uri)
                .map(|(_, uri)| uri.clone())
            else {
                continue;
            };
            if !seen.insert(dep_uri.clone()) {
                continue;
            }
            if let Some(file) = ctx.files.get(&dep_uri) {
                visit(&file.module_imports, &file.module_key, ctx, seen, out);
            }
            out.push(dep_uri);
        }
    }

    let mut seen = HashSet::new();
    let mut out = Vec::new();
    let ctx = DepVisitContext {
        files,
        module_index,
        source_uri,
        project,
    };
    visit(imports, current_module, &ctx, &mut seen, &mut out);
    out
}

fn module_imports_from_ranges<'bump>(
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
) -> Vec<Vec<String>> {
    top_ranges
        .iter()
        .flat_map(|(_, _, top)| module_imports_for_top(top))
        .collect()
}

fn imported_symbol_aliases<'bump>(
    current_module: &ModuleKey,
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
    files: &HashMap<lsp::Url, FileCache>,
    module_index: &[(ModuleKey, lsp::Url)],
    source_uri: &lsp::Url,
    project: Option<&ProjectContext>,
) -> HashMap<String, String> {
    let mut aliases = HashMap::new();
    for (_, _, top) in top_ranges {
        let TopLevel::TLUse(uses, _, _) = unwrap_public(top) else {
            continue;
        };
        for tree in *uses {
            if tree.path.len() < 2 && !tree.wildcard {
                continue;
            }
            let module_path = use_tree_module(tree).unwrap_or_default();
            let modules = project
                .map(|project| project.imported_module_keys(current_module, &module_path))
                .unwrap_or_else(|| fallback_imported_module_keys(current_module, &module_path));
            let Some(module) = modules.into_iter().find(|module| {
                module_index
                    .iter()
                    .any(|(module_key, uri)| module_key == module && uri != source_uri)
            }) else {
                continue;
            };
            let Some(file) = module_index
                .iter()
                .find(|(module_key, _)| module_key == &module)
                .and_then(|(_, uri)| files.get(uri))
            else {
                continue;
            };
            if tree.wildcard {
                for item in &file.exports {
                    let target = file
                        .export_targets
                        .get(item)
                        .cloned()
                        .unwrap_or_else(|| module.join_symbol(item));
                    aliases.insert(item.clone(), target);
                }
                continue;
            }
            let item = tree.path[tree.path.len() - 1].to_string();
            if file.exports.contains(&item) {
                let local = tree
                    .alias
                    .unwrap_or(tree.path[tree.path.len() - 1])
                    .to_string();
                let target = file
                    .export_targets
                    .get(&item)
                    .cloned()
                    .unwrap_or_else(|| module.join_symbol(&item));
                aliases.insert(local, target);
            }
        }
    }
    aliases
}

fn declared_symbol_aliases<'a, 'bump>(
    tops: impl Iterator<Item = &'a TopLevel<'bump>>,
    module: &ModuleKey,
) -> HashMap<String, String>
where
    'bump: 'a,
{
    let mut aliases = HashMap::new();
    for top in tops {
        collect_declared_symbol_aliases(top, module, None, &mut aliases);
    }
    aliases
}

fn collect_declared_symbol_aliases(
    top: &TopLevel<'_>,
    module: &ModuleKey,
    namespace: Option<&str>,
    aliases: &mut HashMap<String, String>,
) {
    match unwrap_public(top) {
        TopLevel::TLDef(name, ..) | TopLevel::TLTheorem(name, ..) => {
            let local = namespace
                .map(|namespace| format!("{namespace}::{name}"))
                .unwrap_or_else(|| (*name).to_string());
            aliases.insert(local.clone(), module.join_symbol(&local));
        }
        TopLevel::TLExternDef(name, ..) => {
            let local = namespace
                .map(|namespace| format!("{namespace}::{name}"))
                .unwrap_or_else(|| (*name).to_string());
            let target = if namespace.is_some() {
                module.join_symbol(&local)
            } else {
                (*name).to_string()
            };
            aliases.insert(local, target);
        }
        TopLevel::TLNamespace(name, items, _) => {
            for item in *items {
                collect_declared_symbol_aliases(item, module, Some(name), aliases);
            }
        }
        _ => {}
    }
}

struct ModuleDiagnosticContext<'a> {
    current_module: &'a ModuleKey,
    files: &'a HashMap<lsp::Url, FileCache>,
    module_index: &'a [(ModuleKey, lsp::Url)],
    uri: &'a lsp::Url,
    project: Option<&'a ProjectContext>,
}

fn use_module_diagnostics<'bump>(
    source: &str,
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
    dirty: &HashSet<usize>,
    ctx: &ModuleDiagnosticContext<'_>,
) -> Vec<(usize, lsp::Diagnostic)> {
    let root = workspace_root_for_uris(std::iter::once(ctx.uri));
    let mut diagnostics = Vec::new();
    let mut imports = Vec::<ImportDiagnosticInfo>::new();
    for (idx, (_, _, top)) in top_ranges.iter().enumerate() {
        match unwrap_public(top) {
            TopLevel::TLUse(uses, visibility, span) => {
                for tree in *uses {
                    if tree.path.len() < 2 && !tree.wildcard {
                        if dirty.contains(&idx) {
                            let message = if matches!(
                                visibility,
                                ligare::front::parser::Visibility::Public
                            ) {
                                "pub use path must include a module and symbol"
                            } else {
                                "use path must include a module and symbol"
                            };
                            diagnostics.push((
                                idx,
                                lsp::Diagnostic {
                                    range: lsp_range_for_span(source, span),
                                    severity: Some(lsp::DiagnosticSeverity::ERROR),
                                    source: Some("ligare".to_string()),
                                    message: message.to_string(),
                                    ..Default::default()
                                },
                            ));
                        }
                        continue;
                    }
                    let local = tree
                        .alias
                        .or_else(|| tree.path.last().copied())
                        .unwrap_or_default()
                        .to_string();
                    let range = lsp_range_for_span(source, span);
                    let module_path = use_tree_module(tree).unwrap_or_default();
                    imports.push(ImportDiagnosticInfo {
                        idx,
                        local,
                        module_path,
                        range,
                    });
                }
            }
            TopLevel::TLMod(name, span) if dirty.contains(&idx) => {
                let module = ctx.current_module.child((*name).to_string());
                if module_file_exists(
                    &module,
                    ctx.files,
                    ctx.module_index,
                    ctx.uri,
                    ctx.project,
                    root.as_deref(),
                ) {
                    continue;
                }
                diagnostics.push((
                    idx,
                    lsp::Diagnostic {
                        range: lsp_range_for_span(source, span),
                        severity: Some(lsp::DiagnosticSeverity::ERROR),
                        source: Some("ligare".to_string()),
                        message: format!("module not found: {}", display_module_key(&module)),
                        ..Default::default()
                    },
                ));
            }
            _ => {}
        }
    }

    let mut imports_by_name = HashMap::<String, Vec<ImportDiagnosticInfo>>::new();
    for import in &imports {
        imports_by_name
            .entry(import.local.clone())
            .or_default()
            .push(import.clone());
        if !dirty.contains(&import.idx) {
            continue;
        }
        if module_exists(
            ctx.current_module,
            &import.module_path,
            ctx.files,
            ctx.module_index,
            ctx.uri,
            ctx.project,
            root.as_deref(),
        ) {
            continue;
        }
        diagnostics.push((
            import.idx,
            lsp::Diagnostic {
                range: import.range,
                severity: Some(lsp::DiagnosticSeverity::ERROR),
                source: Some("ligare".to_string()),
                message: format!("module not found: {}", import.module_path.join("::")),
                ..Default::default()
            },
        ));
    }
    for (local, imports) in imports_by_name {
        if imports.len() < 2 {
            continue;
        }
        for import in imports {
            if !dirty.contains(&import.idx) {
                continue;
            }
            diagnostics.push((
                import.idx,
                lsp::Diagnostic {
                    range: import.range,
                    severity: Some(lsp::DiagnosticSeverity::ERROR),
                    source: Some("ligare".to_string()),
                    message: format!("duplicate import `{local}`"),
                    ..Default::default()
                },
            ));
        }
    }
    diagnostics
}

#[derive(Debug, Clone)]
struct ImportDiagnosticInfo {
    idx: usize,
    local: String,
    module_path: Vec<String>,
    range: lsp::Range,
}

fn module_exists(
    current_module: &ModuleKey,
    module_path: &[String],
    files: &HashMap<lsp::Url, FileCache>,
    module_index: &[(ModuleKey, lsp::Url)],
    source_uri: &lsp::Url,
    project: Option<&ProjectContext>,
    root: Option<&std::path::Path>,
) -> bool {
    let modules = project
        .map(|project| project.imported_module_keys(current_module, module_path))
        .unwrap_or_else(|| fallback_imported_module_keys(current_module, module_path));
    modules
        .into_iter()
        .any(|module| module_file_exists(&module, files, module_index, source_uri, project, root))
}

fn module_file_exists(
    module: &ModuleKey,
    files: &HashMap<lsp::Url, FileCache>,
    module_index: &[(ModuleKey, lsp::Url)],
    source_uri: &lsp::Url,
    project: Option<&ProjectContext>,
    root: Option<&std::path::Path>,
) -> bool {
    module_index
        .iter()
        .any(|(module_key, uri)| module_key == module && uri != source_uri)
        || project
            .map(|project| project.file_candidates(module))
            .or_else(|| root.map(|root| fallback_file_candidates(root, module)))
            .unwrap_or_default()
            .into_iter()
            .any(|path| path.exists())
        || files.values().any(|file| file.module_key == *module)
}

fn lsp_range_for_span(source: &str, span: &std::ops::Range<usize>) -> lsp::Range {
    lsp::Range {
        start: offset_to_position(source, span.start),
        end: offset_to_position(source, span.end.max(span.start)),
    }
}

fn display_module_key(module: &ModuleKey) -> String {
    let mut parts = Vec::new();
    if let Some(package) = &module.package {
        parts.push(package.clone());
    }
    parts.extend(module.path.clone());
    if parts.is_empty() {
        "<root>".to_string()
    } else {
        parts.join("::")
    }
}
