use std::collections::{HashMap, HashSet};

use bumpalo::Bump;
use ligare::checker::CheckMode;
use ligare::compiler::Compiler;
use ligare::compiler::cache::{
    CachedFile, FALLBACK_ROOT_PACKAGE, PackageCompilerCache, now_ms, package_root_for_file,
    source_hash,
};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{DoStmt, Tactic, Term};
use ligare::front::parser::{TopLevel, UseTree};
use tower_lsp::lsp_types as lsp;

use crate::completion::{
    Constraint, Symbol, collect_top_level_symbols, term_signature, top_level_ranges,
};
use crate::diagnostics::{
    DiagnosticCheck, compiler_diagnostic_to_lsp, dedup_diagnostics, parse_error_to_lsp,
};
use crate::navigation::SourceDocument;
use crate::project::{
    ModuleKey, ProjectContext, fallback_file_candidates, fallback_imported_module_keys,
    fallback_module_key, project_context_for_uri, workspace_root_for_uris,
};
use crate::semantic::semantic_tokens_for_source;
use crate::text::offset_to_position;
use crate::{ParseError, parse_program_lsp};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CacheStats {
    pub(crate) file_hits: usize,
    pub(crate) file_misses: usize,
    pub(crate) item_hits: usize,
    pub(crate) item_misses: usize,
    pub(crate) compiler_cache_hits: usize,
    pub(crate) compiler_cache_misses: usize,
}

impl CacheStats {
    #[cfg(test)]
    pub(crate) fn item_hit_rate(&self) -> f64 {
        let total = self.item_hits + self.item_misses;
        if total == 0 {
            1.0
        } else {
            self.item_hits as f64 / total as f64
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CacheUpdate {
    pub(crate) dirty_items: Vec<String>,
    pub(crate) dirty_dependents: Vec<lsp::Url>,
    pub(crate) diagnostics: Vec<lsp::Diagnostic>,
}

#[derive(Debug, Clone)]
pub(crate) struct LspCache {
    files: HashMap<lsp::Url, FileCache>,
    dependents: HashMap<lsp::Url, HashSet<lsp::Url>>,
    stats: CacheStats,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct FileCache {
    text: String,
    version: Option<i32>,
    ast: CachedAst,
    fast_diagnostics: Vec<lsp::Diagnostic>,
    full_diagnostics: Vec<lsp::Diagnostic>,
    semantic_tokens: Vec<lsp::SemanticToken>,
    symbols: Vec<String>,
    exports: Vec<String>,
    items: Vec<ItemCache>,
    module_imports: Vec<Vec<String>>,
    dependencies: HashSet<lsp::Url>,
    module_key: ModuleKey,
    dirty: bool,
}

#[derive(Debug, Clone, Default)]
#[allow(dead_code)]
struct CachedAst {
    items: Vec<CachedAstItem>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct CachedAstItem {
    id: String,
    kind: String,
    range: (usize, usize),
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct ItemCache {
    id: String,
    name: Option<String>,
    range: (usize, usize),
    fingerprint: u64,
    constraint: Option<String>,
    comp_repr: Option<String>,
    dependencies: HashSet<String>,
    diagnostics: Vec<lsp::Diagnostic>,
    full_diagnostics: Vec<lsp::Diagnostic>,
}

#[derive(Debug)]
struct ParsedFile<'bump> {
    ast: crate::Ast<'bump>,
    parse_errors: Vec<ParseError>,
    top_ranges: Vec<(usize, usize, TopLevel<'bump>)>,
    item_infos: Vec<ItemInfo>,
    module_imports: Vec<Vec<String>>,
    symbols: Vec<String>,
    exports: Vec<String>,
}

#[derive(Debug, Clone)]
struct ItemInfo {
    id: String,
    name: Option<String>,
    kind: String,
    range: (usize, usize),
    fingerprint: u64,
    constraint: Option<String>,
    comp_repr: Option<String>,
    dependencies: HashSet<String>,
}

impl LspCache {
    pub(crate) fn new() -> Self {
        Self {
            files: HashMap::new(),
            dependents: HashMap::new(),
            stats: CacheStats::default(),
        }
    }

    pub(crate) fn update_fast(
        &mut self,
        uri: lsp::Url,
        version: Option<i32>,
        text: String,
    ) -> CacheUpdate {
        self.update(uri, version, text, DiagnosticCheck::Fast)
    }

    pub(crate) fn update_full(
        &mut self,
        uri: lsp::Url,
        version: Option<i32>,
        text: String,
    ) -> CacheUpdate {
        self.update(uri, version, text, DiagnosticCheck::Full)
    }

    pub(crate) fn mark_dirty(&mut self, uri: &lsp::Url) {
        if let Some(file) = self.files.get_mut(uri) {
            file.dirty = true;
        }
    }

    pub(crate) fn remove(&mut self, uri: &lsp::Url) {
        self.files.remove(uri);
        self.rebuild_dependents();
    }

    pub(crate) fn text(&self, uri: &lsp::Url) -> Option<String> {
        self.files.get(uri).map(|file| file.text.clone())
    }

    pub(crate) fn version(&self, uri: &lsp::Url) -> Option<i32> {
        self.files.get(uri).and_then(|file| file.version)
    }

    pub(crate) fn semantic_tokens(&self, uri: &lsp::Url) -> Option<Vec<lsp::SemanticToken>> {
        self.files.get(uri).map(|file| file.semantic_tokens.clone())
    }

    pub(crate) fn document_snapshots(&self) -> Vec<SourceDocument> {
        self.files
            .iter()
            .map(|(uri, file)| SourceDocument {
                uri: uri.clone(),
                text: file.text.clone(),
            })
            .collect()
    }

    pub(crate) fn dependency_file_candidates(&self, uri: &lsp::Url) -> Vec<lsp::Url> {
        let Some(file) = self.files.get(uri) else {
            return Vec::new();
        };
        let Some(root) = workspace_root_for_uris(std::iter::once(uri)) else {
            return Vec::new();
        };
        let project = self.project_context_for_cached_uri(uri);
        file.module_imports
            .iter()
            .flat_map(|path| {
                project
                    .as_ref()
                    .map(|project| project.imported_module_keys(&file.module_key, path))
                    .unwrap_or_else(|| fallback_imported_module_keys(&file.module_key, path))
            })
            .flat_map(|module| {
                project
                    .as_ref()
                    .map(|project| project.file_candidates(&module))
                    .unwrap_or_else(|| fallback_file_candidates(&root, &module))
            })
            .filter(|path| path.exists())
            .filter_map(|path| lsp::Url::from_file_path(path).ok())
            .filter(|candidate| candidate != uri && !self.files.contains_key(candidate))
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn stats(&self) -> CacheStats {
        self.stats.clone()
    }

    #[cfg(test)]
    pub(crate) fn cache_summary(&self, uri: &lsp::Url) -> Option<FileCacheSummary> {
        self.files.get(uri).map(|file| FileCacheSummary {
            ast_items: file.ast.items.len(),
            symbols: file.symbols.len(),
            exports: file.exports.clone(),
            items: file.items.len(),
        })
    }

    fn update(
        &mut self,
        uri: lsp::Url,
        version: Option<i32>,
        text: String,
        check: DiagnosticCheck,
    ) -> CacheUpdate {
        let previous = self.files.get(&uri).cloned();
        if previous
            .as_ref()
            .is_some_and(|file| file.text == text && file.version == version && !file.dirty)
        {
            self.stats.file_hits += 1;
            let diagnostics = previous
                .map(|file| diagnostics_for_check(&file, check))
                .unwrap_or_default();
            return CacheUpdate {
                diagnostics,
                ..Default::default()
            };
        }
        self.stats.file_misses += 1;

        let bump = Bump::new();
        let arena = TermArena::new(&bump);
        let parsed = parse_file(&uri, &text, &bump, &arena);
        let semantic_top_ranges =
            crate::completion::expanded_top_level_ranges(&text, &parsed.ast, &bump, &arena);
        let semantic_tokens = semantic_tokens_for_source(&text, &parsed.ast, &semantic_top_ranges);
        let project = self.project_context_for_cached_uri(&uri);
        let module_key = project
            .as_ref()
            .map(|project| project.module_key_for_uri(&uri))
            .unwrap_or_else(|| fallback_module_key(&uri));
        let changed_names = changed_names(previous.as_ref(), &parsed.item_infos);
        let mut dirty_indices =
            dirty_indices(previous.as_ref(), &parsed.item_infos, &changed_names);
        let text_hash = stable_hash(&text);
        let compiler_cache_hit = check == DiagnosticCheck::Full
            && parsed.parse_errors.is_empty()
            && !previous.as_ref().is_some_and(|file| file.dirty)
            && compiler_cache_is_fresh(&uri, text_hash, project.as_ref(), &module_key);
        if compiler_cache_hit {
            self.stats.compiler_cache_hits += 1;
            dirty_indices.clear();
        } else if check == DiagnosticCheck::Full {
            self.stats.compiler_cache_misses += 1;
        }
        self.stats.item_hits += parsed.item_infos.len().saturating_sub(dirty_indices.len());
        self.stats.item_misses += dirty_indices.len();

        let mut items = merge_item_cache(previous.as_ref(), &parsed.item_infos, &dirty_indices);
        let parse_diagnostics = parsed
            .parse_errors
            .iter()
            .cloned()
            .map(|error| parse_error_to_lsp(&text, error))
            .collect::<Vec<_>>();
        let item_diagnostics = check_dirty_items(
            &bump,
            &arena,
            &parsed.top_ranges,
            DirtyCheckContext {
                uri: &uri,
                text: &text,
                dirty: &dirty_indices,
                check,
                files: &self.files,
                project: project.as_ref(),
                module_key: &module_key,
            },
        );
        for (idx, diagnostics) in item_diagnostics {
            if let Some(item) = items.get_mut(idx) {
                match check {
                    DiagnosticCheck::Fast => item.diagnostics = diagnostics,
                    DiagnosticCheck::Full => item.full_diagnostics = diagnostics,
                }
            }
        }

        let mut diagnostics = parse_diagnostics.clone();
        diagnostics.extend(items.iter().flat_map(|item| match check {
            DiagnosticCheck::Fast => item.diagnostics.clone(),
            DiagnosticCheck::Full => {
                if item.full_diagnostics.is_empty() {
                    item.diagnostics.clone()
                } else {
                    item.full_diagnostics.clone()
                }
            }
        }));
        let diagnostics = dedup_diagnostics(diagnostics);
        if check == DiagnosticCheck::Full {
            update_compiler_cache(
                &uri,
                text_hash,
                &module_key,
                &parsed.module_imports,
                &parsed.exports,
                diagnostics.is_empty(),
                project.as_ref(),
            );
        }

        let dependencies = resolve_module_imports(
            &parsed.module_imports,
            &module_key,
            &self.files,
            project.as_ref(),
        );
        let cache = FileCache {
            text,
            version,
            ast: CachedAst {
                items: parsed
                    .item_infos
                    .iter()
                    .map(|item| CachedAstItem {
                        id: item.id.clone(),
                        kind: item.kind.clone(),
                        range: item.range,
                    })
                    .collect(),
            },
            fast_diagnostics: if check == DiagnosticCheck::Fast {
                diagnostics.clone()
            } else {
                previous
                    .as_ref()
                    .map(|file| file.fast_diagnostics.clone())
                    .unwrap_or_default()
            },
            full_diagnostics: if check == DiagnosticCheck::Full {
                diagnostics.clone()
            } else {
                previous
                    .as_ref()
                    .map(|file| file.full_diagnostics.clone())
                    .unwrap_or_default()
            },
            semantic_tokens,
            symbols: parsed.symbols,
            exports: parsed.exports,
            items,
            module_imports: parsed.module_imports,
            dependencies,
            module_key,
            dirty: false,
        };
        self.files.insert(uri.clone(), cache);
        self.rebuild_dependents();
        let mut dirty_dependents = self
            .dependents
            .get(&uri)
            .map(|deps| deps.iter().cloned().collect::<Vec<_>>())
            .unwrap_or_default();
        dirty_dependents.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        for dependent in &dirty_dependents {
            self.mark_dirty(dependent);
        }

        CacheUpdate {
            dirty_items: (0..parsed.item_infos.len())
                .filter(|idx| dirty_indices.contains(idx))
                .filter_map(|idx| parsed.item_infos.get(idx).map(|item| item.id.clone()))
                .collect(),
            dirty_dependents,
            diagnostics,
        }
    }

    fn rebuild_dependents(&mut self) {
        self.dependents.clear();
        let module_index = self
            .files
            .iter()
            .map(|(uri, file)| (file.module_key.clone(), uri.clone()))
            .collect::<Vec<_>>();
        let uris = self.files.keys().cloned().collect::<Vec<_>>();
        for uri in uris {
            let Some(file) = self.files.get(&uri) else {
                continue;
            };
            let project = self.project_context_for_cached_uri(&uri);
            let dependencies = resolve_module_imports_from_index(
                &file.module_imports,
                &file.module_key,
                &module_index,
                &uri,
                project.as_ref(),
            );
            if let Some(file) = self.files.get_mut(&uri) {
                file.dependencies = dependencies;
            }
        }
        for (uri, file) in &self.files {
            for dep in &file.dependencies {
                self.dependents
                    .entry(dep.clone())
                    .or_default()
                    .insert(uri.clone());
            }
        }
    }

    fn project_context_for_cached_uri(&self, uri: &lsp::Url) -> Option<ProjectContext> {
        self.files
            .keys()
            .filter(|existing| *existing != uri)
            .filter_map(project_context_for_uri)
            .find(|project| project.module_key_for_uri(uri).package.is_some())
            .or_else(|| project_context_for_uri(uri))
    }
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FileCacheSummary {
    pub(crate) ast_items: usize,
    pub(crate) symbols: usize,
    pub(crate) exports: Vec<String>,
    pub(crate) items: usize,
}

fn diagnostics_for_check(file: &FileCache, check: DiagnosticCheck) -> Vec<lsp::Diagnostic> {
    match check {
        DiagnosticCheck::Fast => file.fast_diagnostics.clone(),
        DiagnosticCheck::Full => {
            if file.full_diagnostics.is_empty() {
                file.fast_diagnostics.clone()
            } else {
                file.full_diagnostics.clone()
            }
        }
    }
}

fn parse_file<'bump>(
    uri: &lsp::Url,
    text: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> ParsedFile<'bump> {
    let (ast, parse_errors) = parse_program_lsp(text, bump, arena);
    let top_ranges = top_level_ranges(text, &ast);
    let mut module_imports = Vec::new();
    let mut symbols = Vec::new();
    let mut exports = Vec::new();
    let mut item_infos = Vec::new();

    for (idx, (start, end, top)) in top_ranges.iter().enumerate() {
        let source = text.get(*start..*end).unwrap_or_default();
        let mut top_symbols = Vec::<Symbol>::new();
        collect_top_level_symbols(top, &mut top_symbols);
        symbols.extend(top_symbols.iter().map(|symbol| symbol.name.clone()));
        exports.extend(exported_names(top));
        module_imports.extend(module_imports_for_top(top));
        item_infos.push(ItemInfo {
            id: item_id(idx, top),
            name: item_name(top),
            kind: item_kind(top).to_string(),
            range: (*start, *end),
            fingerprint: stable_hash(source),
            constraint: item_constraint(top),
            comp_repr: Some(format!("{:?}", unwrap_public(top))),
            dependencies: item_dependencies(top),
        });
    }

    if item_infos.is_empty() && !parse_errors.is_empty() {
        item_infos.push(ItemInfo {
            id: format!("parse@{}", uri.path()),
            name: None,
            kind: "parse-error".to_string(),
            range: (0, text.len()),
            fingerprint: stable_hash(text),
            constraint: None,
            comp_repr: None,
            dependencies: HashSet::new(),
        });
    }

    ParsedFile {
        ast,
        parse_errors,
        top_ranges,
        item_infos,
        module_imports,
        symbols,
        exports,
    }
}

fn changed_names(previous: Option<&FileCache>, current: &[ItemInfo]) -> HashSet<String> {
    let previous_by_id = previous
        .map(|file| {
            file.items
                .iter()
                .map(|item| (item.id.clone(), item))
                .collect::<HashMap<_, _>>()
        })
        .unwrap_or_default();
    current
        .iter()
        .filter(|item| {
            previous_by_id
                .get(&item.id)
                .is_none_or(|previous| previous.fingerprint != item.fingerprint)
        })
        .filter_map(|item| item.name.clone())
        .collect()
}

fn dirty_indices(
    previous: Option<&FileCache>,
    current: &[ItemInfo],
    changed_names: &HashSet<String>,
) -> HashSet<usize> {
    let previous_by_id = previous
        .map(|file| {
            file.items
                .iter()
                .map(|item| (item.id.clone(), item))
                .collect::<HashMap<_, _>>()
        })
        .unwrap_or_default();
    let mut dirty = HashSet::new();
    for (idx, item) in current.iter().enumerate() {
        let changed = previous_by_id
            .get(&item.id)
            .is_none_or(|previous| previous.fingerprint != item.fingerprint);
        if changed
            || item
                .dependencies
                .iter()
                .any(|dep| changed_names.contains(dep))
        {
            dirty.insert(idx);
        }
    }
    if previous.is_some_and(|file| file.dirty) {
        for (idx, item) in current.iter().enumerate() {
            if !item.dependencies.is_empty() || item.name.is_some() {
                dirty.insert(idx);
            }
        }
    }
    dirty
}

fn merge_item_cache(
    previous: Option<&FileCache>,
    current: &[ItemInfo],
    dirty: &HashSet<usize>,
) -> Vec<ItemCache> {
    let previous_by_id = previous
        .map(|file| {
            file.items
                .iter()
                .map(|item| (item.id.clone(), item.clone()))
                .collect::<HashMap<_, _>>()
        })
        .unwrap_or_default();
    current
        .iter()
        .enumerate()
        .map(|(idx, item)| {
            if !dirty.contains(&idx)
                && let Some(previous) = previous_by_id.get(&item.id)
            {
                return previous.clone();
            }
            ItemCache {
                id: item.id.clone(),
                name: item.name.clone(),
                range: item.range,
                fingerprint: item.fingerprint,
                constraint: item.constraint.clone(),
                comp_repr: item.comp_repr.clone(),
                dependencies: item.dependencies.clone(),
                diagnostics: Vec::new(),
                full_diagnostics: Vec::new(),
            }
        })
        .collect()
}

struct DirtyCheckContext<'a> {
    uri: &'a lsp::Url,
    text: &'a str,
    dirty: &'a HashSet<usize>,
    check: DiagnosticCheck,
    files: &'a HashMap<lsp::Url, FileCache>,
    project: Option<&'a ProjectContext>,
    module_key: &'a ModuleKey,
}

fn check_dirty_items<'bump>(
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
                    aliases.insert(item.clone(), module.join_symbol(item));
                }
                continue;
            }
            let item = tree.path[tree.path.len() - 1].to_string();
            if file.exports.contains(&item) {
                let local = tree
                    .alias
                    .unwrap_or(tree.path[tree.path.len() - 1])
                    .to_string();
                aliases.insert(local, module.join_symbol(&item));
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

#[derive(Default)]
struct RewriteScope {
    locals: Vec<String>,
}

impl RewriteScope {
    fn contains(&self, name: &str) -> bool {
        self.locals.iter().rev().any(|local| local == name)
    }

    fn push(&mut self, name: &str) {
        self.locals.push(name.to_string());
    }

    fn pop(&mut self) {
        self.locals.pop();
    }
}

fn rewrite_top_for_module<'bump>(
    arena: &'bump TermArena<'bump>,
    top: &TopLevel<'bump>,
    imports: &HashMap<String, String>,
    own_names: &HashMap<String, String>,
) -> Vec<TopLevel<'bump>> {
    match unwrap_public(top) {
        TopLevel::TLDef(name, params, ret, body, span) => {
            let qname = own_names.get(*name).map(String::as_str).unwrap_or(name);
            let qname = arena.alloc_str(qname);
            let mut scope = RewriteScope::default();
            for (param, _) in params.iter().rev() {
                scope.push(param);
            }
            let params = rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let ret = ret
                .map(|term| rewrite_term_for_module(arena, term, imports, own_names, &mut scope));
            let body = rewrite_term_for_module(arena, body, imports, own_names, &mut scope);
            vec![TopLevel::TLDef(qname, params, ret, body, span.clone())]
        }
        TopLevel::TLExternDef(name, params, ret, span) => {
            let mut scope = RewriteScope::default();
            for (param, _) in params.iter().rev() {
                scope.push(param);
            }
            let params = rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let ret = rewrite_term_for_module(arena, ret, imports, own_names, &mut scope);
            vec![TopLevel::TLExternDef(name, params, ret, span.clone())]
        }
        TopLevel::TLInstance(name, constraint, value, span) => {
            let qname = own_names.get(*name).map(String::as_str).unwrap_or(name);
            let qname = arena.alloc_str(qname);
            vec![TopLevel::TLInstance(
                qname,
                rewrite_term_for_module(
                    arena,
                    constraint,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                rewrite_term_for_module(
                    arena,
                    value,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                span.clone(),
            )]
        }
        TopLevel::TLVariable(params, span) => vec![TopLevel::TLVariable(
            rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLTheorem(name, prop, body, span) => {
            let qname = own_names.get(*name).map(String::as_str).unwrap_or(name);
            let qname = arena.alloc_str(qname);
            let prop = rewrite_term_for_module(
                arena,
                prop,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let body = rewrite_term_for_module(
                arena,
                body,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            vec![TopLevel::TLTheorem(qname, prop, body, span.clone())]
        }
        TopLevel::TLCheck(term, constraint, span) => vec![TopLevel::TLCheck(
            rewrite_term_for_module(
                arena,
                term,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            rewrite_term_for_module(
                arena,
                constraint,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLEval(term, span) => vec![TopLevel::TLEval(
            rewrite_term_for_module(
                arena,
                term,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLExpr(term, span) => vec![TopLevel::TLExpr(
            rewrite_term_for_module(
                arena,
                term,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLSplice(term, span) => vec![TopLevel::TLSplice(
            rewrite_term_for_module(
                arena,
                term,
                imports,
                own_names,
                &mut RewriteScope::default(),
            ),
            span.clone(),
        )],
        TopLevel::TLNamespace(name, items, _) => {
            let mut rewritten = Vec::new();
            for item in *items {
                rewrite_namespace_item_for_module(
                    arena,
                    name,
                    item,
                    imports,
                    own_names,
                    &mut rewritten,
                );
            }
            rewritten
        }
        TopLevel::TLUse(..)
        | TopLevel::TLMod(..)
        | TopLevel::TLPublic(_)
        | TopLevel::TLAttributed(..) => Vec::new(),
    }
}

fn rewrite_namespace_item_for_module<'bump>(
    arena: &'bump TermArena<'bump>,
    namespace: &str,
    top: &TopLevel<'bump>,
    imports: &HashMap<String, String>,
    own_names: &HashMap<String, String>,
    out: &mut Vec<TopLevel<'bump>>,
) {
    match unwrap_public(top) {
        TopLevel::TLDef(name, params, ret, body, span) => {
            let local = format!("{namespace}::{name}");
            let qname = own_names
                .get(&local)
                .map(String::as_str)
                .unwrap_or(local.as_str());
            let qname = arena.alloc_str(qname);
            let mut scope = RewriteScope::default();
            for (param, _) in params.iter().rev() {
                scope.push(param);
            }
            let params = rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let ret = ret
                .map(|term| rewrite_term_for_module(arena, term, imports, own_names, &mut scope));
            let body = rewrite_term_for_module(arena, body, imports, own_names, &mut scope);
            out.push(TopLevel::TLDef(qname, params, ret, body, span.clone()));
        }
        TopLevel::TLExternDef(name, params, ret, span) => {
            let local = format!("{namespace}::{name}");
            let qname = own_names
                .get(&local)
                .map(String::as_str)
                .unwrap_or(local.as_str());
            let qname = arena.alloc_str(qname);
            let mut scope = RewriteScope::default();
            for (param, _) in params.iter().rev() {
                scope.push(param);
            }
            let params = rewrite_params_for_module(
                arena,
                params,
                imports,
                own_names,
                &mut RewriteScope::default(),
            );
            let ret = rewrite_term_for_module(arena, ret, imports, own_names, &mut scope);
            out.push(TopLevel::TLExternDef(qname, params, ret, span.clone()));
        }
        TopLevel::TLInstance(name, constraint, value, span) => {
            let local = format!("{namespace}::{name}");
            let qname = own_names
                .get(&local)
                .map(String::as_str)
                .unwrap_or(local.as_str());
            let qname = arena.alloc_str(qname);
            out.push(TopLevel::TLInstance(
                qname,
                rewrite_term_for_module(
                    arena,
                    constraint,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                rewrite_term_for_module(
                    arena,
                    value,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                span.clone(),
            ));
        }
        TopLevel::TLVariable(params, span) => {
            out.push(TopLevel::TLVariable(
                rewrite_params_for_module(
                    arena,
                    params,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                span.clone(),
            ));
        }
        TopLevel::TLTheorem(name, prop, body, span) => {
            let local = format!("{namespace}::{name}");
            let qname = own_names
                .get(&local)
                .map(String::as_str)
                .unwrap_or(local.as_str());
            let qname = arena.alloc_str(qname);
            out.push(TopLevel::TLTheorem(
                qname,
                rewrite_term_for_module(
                    arena,
                    prop,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                rewrite_term_for_module(
                    arena,
                    body,
                    imports,
                    own_names,
                    &mut RewriteScope::default(),
                ),
                span.clone(),
            ));
        }
        _ => {}
    }
}

fn rewrite_params_for_module<'bump>(
    arena: &'bump TermArena<'bump>,
    params: &'bump [(&'bump str, Option<&'bump Term<'bump>>)],
    imports: &HashMap<String, String>,
    own_names: &HashMap<String, String>,
    scope: &mut RewriteScope,
) -> &'bump [(&'bump str, Option<&'bump Term<'bump>>)] {
    let mut rewritten = Vec::new();
    for (name, constraint) in params {
        let constraint =
            constraint.map(|term| rewrite_term_for_module(arena, term, imports, own_names, scope));
        rewritten.push((*name, constraint));
        scope.push(name);
    }
    arena.alloc_slice(&rewritten)
}

fn rewrite_term_for_module<'bump>(
    arena: &'bump TermArena<'bump>,
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
                return arena.named(arena.alloc_str(full));
            }
            term
        }
        Term::Builtin(_) | Term::Global(_) => term,
        Term::App(f, a) => arena.app(
            rewrite_term_for_module(arena, f, imports, own_names, scope),
            rewrite_term_for_module(arena, a, imports, own_names, scope),
        ),
        Term::Implicit(inner) => arena.implicit(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::NamedLam(name, body) => {
            scope.push(name);
            let body = rewrite_term_for_module(arena, body, imports, own_names, scope);
            scope.pop();
            arena.named_lam(name, body)
        }
        Term::Lam(body) => arena.lam(rewrite_term_for_module(
            arena, body, imports, own_names, scope,
        )),
        Term::Pi(name, a, b) => {
            let a = rewrite_term_for_module(arena, a, imports, own_names, scope);
            scope.push(name);
            let b = rewrite_term_for_module(arena, b, imports, own_names, scope);
            scope.pop();
            arena.pi(name, a, b)
        }
        Term::Let(name, value, body, constraint) => {
            let value = rewrite_term_for_module(arena, value, imports, own_names, scope);
            let constraint = constraint
                .map(|term| rewrite_term_for_module(arena, term, imports, own_names, scope));
            scope.push(name);
            let body = rewrite_term_for_module(arena, body, imports, own_names, scope);
            scope.pop();
            arena.let_(name, value, body, constraint)
        }
        Term::IfThenElse(cond, then_branch, else_branch) => arena.if_then_else(
            rewrite_term_for_module(arena, cond, imports, own_names, scope),
            rewrite_term_for_module(arena, then_branch, imports, own_names, scope),
            rewrite_term_for_module(arena, else_branch, imports, own_names, scope),
        ),
        Term::Refine(name, parent, predicate) => {
            let parent = rewrite_term_for_module(arena, parent, imports, own_names, scope);
            scope.push(name);
            let predicate = rewrite_term_for_module(arena, predicate, imports, own_names, scope);
            scope.pop();
            arena.refine(name, parent, predicate)
        }
        Term::Annot(inner, constraint) => arena.annot(
            rewrite_term_for_module(arena, inner, imports, own_names, scope),
            rewrite_term_for_module(arena, constraint, imports, own_names, scope),
        ),
        Term::ByProof(inner, tactics) => {
            let inner =
                inner.map(|term| rewrite_term_for_module(arena, term, imports, own_names, scope));
            let tactics = tactics
                .iter()
                .map(|tactic| match tactic {
                    Tactic::Exact(term) => Tactic::Exact(rewrite_term_for_module(
                        arena, term, imports, own_names, scope,
                    )),
                    Tactic::Apply(term) => Tactic::Apply(rewrite_term_for_module(
                        arena, term, imports, own_names, scope,
                    )),
                    Tactic::Intro(name) => Tactic::Intro(*name),
                    Tactic::Have(name, term) => Tactic::Have(
                        name,
                        rewrite_term_for_module(arena, term, imports, own_names, scope),
                    ),
                    Tactic::Custom(name, args) => {
                        let args = args
                            .iter()
                            .map(|arg| {
                                rewrite_term_for_module(arena, arg, imports, own_names, scope)
                            })
                            .collect::<Vec<_>>();
                        Tactic::Custom(name, arena.alloc_slice(&args))
                    }
                })
                .collect::<Vec<_>>();
            arena.by_proof(inner, arena.alloc_slice(&tactics))
        }
        Term::EnumDef(name, variants) => {
            let qname = qualify_type_name(arena, name, own_names);
            let variants = variants
                .iter()
                .map(|(variant, fields)| {
                    let qvariant = qualify_type_name(arena, variant, own_names);
                    let fields = fields
                        .iter()
                        .map(|(field, constraint)| {
                            (
                                *field,
                                rewrite_term_for_module(
                                    arena, constraint, imports, own_names, scope,
                                ),
                            )
                        })
                        .collect::<Vec<_>>();
                    (qvariant, arena.alloc_slice(&fields))
                })
                .collect::<Vec<_>>();
            arena.enum_def(qname, arena.alloc_slice(&variants))
        }
        Term::StructDef(name, fields) => {
            let qname = qualify_type_name(arena, name, own_names);
            let fields = fields
                .iter()
                .map(|(field, constraint)| {
                    (
                        *field,
                        rewrite_term_for_module(arena, constraint, imports, own_names, scope),
                    )
                })
                .collect::<Vec<_>>();
            arena.struct_def(qname, arena.alloc_slice(&fields))
        }
        Term::Variant(name, index, payloads) => {
            let qname = qualify_type_name(arena, name, own_names);
            let payloads = payloads
                .iter()
                .map(|payload| rewrite_term_for_module(arena, payload, imports, own_names, scope))
                .collect::<Vec<_>>();
            arena.variant(qname, *index, arena.alloc_slice(&payloads))
        }
        Term::StructCons(name, payloads) => {
            let qname = qualify_type_name(arena, name, own_names);
            let payloads = payloads
                .iter()
                .map(|payload| rewrite_term_for_module(arena, payload, imports, own_names, scope))
                .collect::<Vec<_>>();
            arena.struct_cons(qname, arena.alloc_slice(&payloads))
        }
        Term::Match(scrutinee, branches) => {
            let scrutinee = rewrite_term_for_module(arena, scrutinee, imports, own_names, scope);
            let branches = branches
                .iter()
                .map(|(variant, binds, body)| {
                    for (name, _) in binds.iter().rev() {
                        scope.push(name);
                    }
                    let body = rewrite_term_for_module(arena, body, imports, own_names, scope);
                    for _ in *binds {
                        scope.pop();
                    }
                    let binds = binds
                        .iter()
                        .map(|(name, constraint)| {
                            (
                                *name,
                                rewrite_term_for_module(
                                    arena, constraint, imports, own_names, scope,
                                ),
                            )
                        })
                        .collect::<Vec<_>>();
                    (*variant, arena.alloc_slice(&binds), body)
                })
                .collect::<Vec<_>>();
            arena.match_(scrutinee, arena.alloc_slice(&branches))
        }
        Term::NamedMatch(scrutinee, branches) => {
            let scrutinee = rewrite_term_for_module(arena, scrutinee, imports, own_names, scope);
            let branches = branches
                .iter()
                .map(|(variant, binds, body)| {
                    let qvariant = qualify_type_name(arena, variant, own_names);
                    for (name, _) in binds.iter().rev() {
                        scope.push(name);
                    }
                    let body = rewrite_term_for_module(arena, body, imports, own_names, scope);
                    for _ in *binds {
                        scope.pop();
                    }
                    let binds = binds
                        .iter()
                        .map(|(name, constraint)| {
                            (
                                *name,
                                rewrite_term_for_module(
                                    arena, constraint, imports, own_names, scope,
                                ),
                            )
                        })
                        .collect::<Vec<_>>();
                    (qvariant, arena.alloc_slice(&binds), body)
                })
                .collect::<Vec<_>>();
            arena.named_match(scrutinee, arena.alloc_slice(&branches))
        }
        Term::Do(stmts) => {
            let stmts = stmts
                .iter()
                .map(|stmt| match stmt {
                    DoStmt::Bind(name, rhs) => DoStmt::Bind(
                        name,
                        rewrite_term_for_module(arena, rhs, imports, own_names, scope),
                    ),
                    DoStmt::Let(name, rhs, constraint) => {
                        let rhs = rewrite_term_for_module(arena, rhs, imports, own_names, scope);
                        let constraint = constraint.map(|constraint| {
                            rewrite_term_for_module(arena, constraint, imports, own_names, scope)
                        });
                        DoStmt::Let(name, rhs, constraint)
                    }
                    DoStmt::Expr(expr) => DoStmt::Expr(rewrite_term_for_module(
                        arena, expr, imports, own_names, scope,
                    )),
                })
                .collect::<Vec<_>>();
            arena.do_(arena.alloc_slice(&stmts))
        }
        Term::StructProj(inner, index) => arena.struct_proj(
            rewrite_term_for_module(arena, inner, imports, own_names, scope),
            *index,
        ),
        Term::MethodCall(receiver, method) => arena.method_call(
            rewrite_term_for_module(arena, receiver, imports, own_names, scope),
            method,
        ),
        Term::Unsafe(inner) => arena.unsafe_(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::Pure(inner) => arena.pure(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::Quote(inner) => arena.quote(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::Splice(inner) => arena.splice(rewrite_term_for_module(
            arena, inner, imports, own_names, scope,
        )),
        Term::Var(_)
        | Term::LitInt(_)
        | Term::LitBool(_)
        | Term::LitStr(_)
        | Term::PrimOp(_)
        | Term::Universe(_)
        | Term::AutoProof
        | Term::RefParam => term,
    }
}

fn qualify_type_name<'bump>(
    arena: &'bump TermArena<'bump>,
    name: &'bump str,
    own_names: &HashMap<String, String>,
) -> &'bump str {
    own_names
        .get(name)
        .map(|name| arena.alloc_str(name))
        .unwrap_or(name)
}

fn item_id(idx: usize, top: &TopLevel<'_>) -> String {
    item_name(top).unwrap_or_else(|| format!("{}@{idx}", item_kind(top)))
}

fn item_name(top: &TopLevel<'_>) -> Option<String> {
    match unwrap_public(top) {
        TopLevel::TLDef(name, ..)
        | TopLevel::TLExternDef(name, ..)
        | TopLevel::TLInstance(name, ..)
        | TopLevel::TLTheorem(name, ..)
        | TopLevel::TLMod(name, _)
        | TopLevel::TLNamespace(name, _, _) => Some((*name).to_string()),
        TopLevel::TLUse(uses, _, _) => uses
            .first()
            .and_then(|tree| tree.alias.or_else(|| tree.path.last().copied()))
            .map(str::to_string),
        TopLevel::TLVariable(..)
        | TopLevel::TLCheck(..)
        | TopLevel::TLEval(..)
        | TopLevel::TLExpr(..)
        | TopLevel::TLSplice(..) => None,
        TopLevel::TLPublic(_) | TopLevel::TLAttributed(..) => unreachable!(),
    }
}

fn item_kind(top: &TopLevel<'_>) -> &'static str {
    match unwrap_public(top) {
        TopLevel::TLDef(..) => "def",
        TopLevel::TLExternDef(..) => "extern",
        TopLevel::TLInstance(..) => "instance",
        TopLevel::TLVariable(..) => "variable",
        TopLevel::TLTheorem(..) => "theorem",
        TopLevel::TLUse(..) => "use",
        TopLevel::TLMod(..) => "mod",
        TopLevel::TLNamespace(..) => "namespace",
        TopLevel::TLCheck(..) => "check",
        TopLevel::TLEval(..) => "eval",
        TopLevel::TLExpr(..) => "expr",
        TopLevel::TLSplice(..) => "splice",
        TopLevel::TLPublic(_) | TopLevel::TLAttributed(..) => unreachable!(),
    }
}

fn item_constraint(top: &TopLevel<'_>) -> Option<String> {
    match unwrap_public(top) {
        TopLevel::TLDef(_, params, ret, body, _) => {
            if params.is_empty() {
                term_signature(body)
                    .map(|sig| sig.whole.display)
                    .or_else(|| ret.map(|term| Constraint::from_term(term).display))
            } else {
                ret.map(|term| Constraint::from_term(term).display)
            }
        }
        TopLevel::TLExternDef(_, _, ret, _) => Some(Constraint::from_term(ret).display),
        TopLevel::TLInstance(_, constraint, _, _) => {
            Some(Constraint::from_term(constraint).display)
        }
        TopLevel::TLVariable(..) => None,
        TopLevel::TLTheorem(_, prop, _, _) | TopLevel::TLCheck(_, prop, _) => {
            Some(Constraint::from_term(prop).display)
        }
        TopLevel::TLUse(..)
        | TopLevel::TLMod(..)
        | TopLevel::TLNamespace(..)
        | TopLevel::TLEval(..)
        | TopLevel::TLExpr(..)
        | TopLevel::TLSplice(..) => None,
        TopLevel::TLPublic(_) | TopLevel::TLAttributed(..) => unreachable!(),
    }
}

fn item_dependencies(top: &TopLevel<'_>) -> HashSet<String> {
    let mut names = HashSet::new();
    if let TopLevel::TLAttributed(attrs, inner, _) = top {
        for attr in *attrs {
            if attr.is_name("derive") {
                for arg in attr.args {
                    if let Some(trait_name) = attr_arg_name(arg) {
                        if let Some((prefix, leaf)) = trait_name.rsplit_once("::") {
                            names.insert(format!("{prefix}::derive_{leaf}"));
                        } else {
                            names.insert(format!("derive_{trait_name}"));
                        }
                    }
                    collect_term_names(arg, &mut names);
                }
            } else {
                names.insert(attr.path.join("::"));
                for arg in attr.args {
                    collect_term_names(arg, &mut names);
                }
            }
        }
        names.extend(item_dependencies(inner));
        if let Some(name) = item_name(top) {
            names.remove(&name);
        }
        return names;
    }
    match unwrap_public(top) {
        TopLevel::TLDef(_, params, ret, body, _) => {
            for (_, constraint) in *params {
                if let Some(constraint) = constraint {
                    collect_term_names(constraint, &mut names);
                }
            }
            if let Some(ret) = ret {
                collect_term_names(ret, &mut names);
            }
            collect_term_names(body, &mut names);
        }
        TopLevel::TLExternDef(_, params, ret, _) => {
            for (_, constraint) in *params {
                if let Some(constraint) = constraint {
                    collect_term_names(constraint, &mut names);
                }
            }
            collect_term_names(ret, &mut names);
        }
        TopLevel::TLInstance(_, constraint, value, _) => {
            collect_term_names(constraint, &mut names);
            collect_term_names(value, &mut names);
        }
        TopLevel::TLVariable(params, _) => {
            for (_, constraint) in *params {
                if let Some(constraint) = constraint {
                    collect_term_names(constraint, &mut names);
                }
            }
        }
        TopLevel::TLTheorem(_, prop, body, _) => {
            collect_term_names(prop, &mut names);
            collect_term_names(body, &mut names);
        }
        TopLevel::TLCheck(term, constraint, _) => {
            collect_term_names(term, &mut names);
            collect_term_names(constraint, &mut names);
        }
        TopLevel::TLEval(term, _) | TopLevel::TLExpr(term, _) | TopLevel::TLSplice(term, _) => {
            collect_term_names(term, &mut names)
        }
        TopLevel::TLUse(..) | TopLevel::TLMod(..) => {}
        TopLevel::TLNamespace(_, items, _) => {
            for item in *items {
                names.extend(item_dependencies(item));
            }
        }
        TopLevel::TLPublic(_) | TopLevel::TLAttributed(..) => unreachable!(),
    }
    if let Some(name) = item_name(top) {
        names.remove(&name);
    }
    names
}

fn attr_arg_name(term: &Term<'_>) -> Option<String> {
    match term {
        Term::Named(name) | Term::Global(name) | Term::Builtin(name) => Some((*name).to_string()),
        _ => None,
    }
}

fn collect_term_names(term: &Term<'_>, names: &mut HashSet<String>) {
    match term {
        Term::Named(name) | Term::Global(name) => {
            names.insert((*name).to_string());
        }
        Term::Implicit(inner) => collect_term_names(inner, names),
        Term::App(f, a) => {
            collect_term_names(f, names);
            collect_term_names(a, names);
        }
        Term::Lam(body)
        | Term::NamedLam(_, body)
        | Term::Unsafe(body)
        | Term::Pure(body)
        | Term::Quote(body)
        | Term::Splice(body)
        | Term::StructProj(body, _)
        | Term::MethodCall(body, _) => {
            collect_term_names(body, names);
        }
        Term::Pi(_, a, b) | Term::Refine(_, a, b) | Term::Annot(a, b) => {
            collect_term_names(a, names);
            collect_term_names(b, names);
        }
        Term::Let(_, value, body, constraint) => {
            collect_term_names(value, names);
            collect_term_names(body, names);
            if let Some(constraint) = constraint {
                collect_term_names(constraint, names);
            }
        }
        Term::IfThenElse(c, t, f) => {
            collect_term_names(c, names);
            collect_term_names(t, names);
            collect_term_names(f, names);
        }
        Term::ByProof(inner, tactics) => {
            if let Some(inner) = inner {
                collect_term_names(inner, names);
            }
            for tactic in *tactics {
                match tactic {
                    Tactic::Exact(term) | Tactic::Apply(term) | Tactic::Have(_, term) => {
                        collect_term_names(term, names);
                    }
                    Tactic::Custom(_, args) => {
                        for arg in *args {
                            collect_term_names(arg, names);
                        }
                    }
                    Tactic::Intro(_) => {}
                }
            }
        }
        Term::EnumDef(_, variants) => {
            for (_, fields) in *variants {
                for (_, constraint) in *fields {
                    collect_term_names(constraint, names);
                }
            }
        }
        Term::Variant(_, _, payloads) | Term::StructCons(_, payloads) => {
            for payload in *payloads {
                collect_term_names(payload, names);
            }
        }
        Term::Match(scrutinee, branches) => {
            collect_term_names(scrutinee, names);
            for (_, binds, body) in *branches {
                for (_, constraint) in *binds {
                    collect_term_names(constraint, names);
                }
                collect_term_names(body, names);
            }
        }
        Term::NamedMatch(scrutinee, branches) => {
            collect_term_names(scrutinee, names);
            for (_, binds, body) in *branches {
                for (_, constraint) in *binds {
                    collect_term_names(constraint, names);
                }
                collect_term_names(body, names);
            }
        }
        Term::Do(stmts) => {
            for stmt in *stmts {
                match stmt {
                    DoStmt::Bind(_, term) | DoStmt::Expr(term) => collect_term_names(term, names),
                    DoStmt::Let(_, term, constraint) => {
                        collect_term_names(term, names);
                        if let Some(constraint) = constraint {
                            collect_term_names(constraint, names);
                        }
                    }
                }
            }
        }
        Term::StructDef(_, fields) => {
            for (_, constraint) in *fields {
                collect_term_names(constraint, names);
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

fn exported_names(top: &TopLevel<'_>) -> Vec<String> {
    match top {
        TopLevel::TLPublic(inner) => item_name(inner).into_iter().collect(),
        TopLevel::TLUse(_, ligare::front::parser::Visibility::Public, _) => {
            item_name(top).into_iter().collect()
        }
        _ => Vec::new(),
    }
}

fn module_imports_for_top(top: &TopLevel<'_>) -> Vec<Vec<String>> {
    let mut imports = match unwrap_public(top) {
        TopLevel::TLUse(uses, _, _) => uses.iter().filter_map(use_tree_module).collect(),
        TopLevel::TLMod(name, _) => vec![vec![(*name).to_string()]],
        _ => Vec::new(),
    };
    imports.extend(qualified_module_imports_for_top(top));
    imports.sort();
    imports.dedup();
    imports
}

fn qualified_module_imports_for_top(top: &TopLevel<'_>) -> Vec<Vec<String>> {
    item_dependencies(top)
        .into_iter()
        .filter_map(|name| {
            let mut parts = name.split("::").map(str::to_string).collect::<Vec<_>>();
            (parts.len() > 1).then(|| {
                parts.pop();
                parts
            })
        })
        .collect()
}

fn use_tree_module(tree: &UseTree<'_>) -> Option<Vec<String>> {
    if tree.wildcard {
        return (!tree.path.is_empty())
            .then(|| tree.path.iter().map(|part| (*part).to_string()).collect());
    }
    (tree.path.len() > 1).then(|| {
        tree.path[..tree.path.len() - 1]
            .iter()
            .map(|part| (*part).to_string())
            .collect()
    })
}

fn resolve_module_imports(
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

fn resolve_module_imports_from_index(
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

fn unwrap_public<'a, 'bump>(top: &'a TopLevel<'bump>) -> &'a TopLevel<'bump> {
    match top {
        TopLevel::TLPublic(inner) => unwrap_public(inner),
        TopLevel::TLAttributed(_, inner, _) => unwrap_public(inner),
        other => other,
    }
}

fn stable_hash(value: &str) -> u64 {
    source_hash(value)
}

fn compiler_cache_is_fresh(
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

fn update_compiler_cache(
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
