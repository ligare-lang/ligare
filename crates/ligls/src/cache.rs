use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use bumpalo::Bump;
use ligare::checker::CheckMode;
use ligare::compiler::Compiler;
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
use crate::{ParseError, parse_program_lsp};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CacheStats {
    pub(crate) file_hits: usize,
    pub(crate) file_misses: usize,
    pub(crate) item_hits: usize,
    pub(crate) item_misses: usize,
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
        let semantic_tokens = semantic_tokens_for_source(&text, &parsed.ast, &parsed.top_ranges);
        let changed_names = changed_names(previous.as_ref(), &parsed.item_infos);
        let dirty_indices = dirty_indices(previous.as_ref(), &parsed.item_infos, &changed_names);
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
            &text,
            &parsed.top_ranges,
            &dirty_indices,
            check,
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

        let project = self.project_context_for_cached_uri(&uri);
        let module_key = project
            .as_ref()
            .map(|project| project.module_key_for_uri(&uri))
            .unwrap_or_else(|| fallback_module_key(&uri));
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

fn check_dirty_items<'bump>(
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
    text: &str,
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
    dirty: &HashSet<usize>,
    check: DiagnosticCheck,
) -> HashMap<usize, Vec<lsp::Diagnostic>> {
    let mut compiler = Compiler::new(bump, arena);
    let diagnostics = compiler.check_top_levels_incremental_for_diagnostics(
        top_ranges
            .iter()
            .enumerate()
            .map(|(idx, (_, _, top))| (idx, top.clone(), dirty.contains(&idx))),
        "<lsp>",
        text,
        CheckMode::from(check),
    );
    let mut by_item = HashMap::<usize, Vec<lsp::Diagnostic>>::new();
    for (idx, diagnostic) in diagnostics {
        by_item
            .entry(idx)
            .or_default()
            .push(compiler_diagnostic_to_lsp(text, diagnostic));
    }
    by_item
}

fn item_id(idx: usize, top: &TopLevel<'_>) -> String {
    item_name(top).unwrap_or_else(|| format!("{}@{idx}", item_kind(top)))
}

fn item_name(top: &TopLevel<'_>) -> Option<String> {
    match unwrap_public(top) {
        TopLevel::TLDef(name, ..)
        | TopLevel::TLExternDef(name, ..)
        | TopLevel::TLTheorem(name, ..)
        | TopLevel::TLMod(name, _) => Some((*name).to_string()),
        TopLevel::TLUse(uses, _, _) => uses
            .first()
            .and_then(|tree| tree.alias.or_else(|| tree.path.last().copied()))
            .map(str::to_string),
        TopLevel::TLCheck(..) | TopLevel::TLEval(..) | TopLevel::TLExpr(..) => None,
        TopLevel::TLPublic(_) => unreachable!(),
    }
}

fn item_kind(top: &TopLevel<'_>) -> &'static str {
    match unwrap_public(top) {
        TopLevel::TLDef(..) => "def",
        TopLevel::TLExternDef(..) => "extern",
        TopLevel::TLTheorem(..) => "theorem",
        TopLevel::TLUse(..) => "use",
        TopLevel::TLMod(..) => "mod",
        TopLevel::TLCheck(..) => "check",
        TopLevel::TLEval(..) => "eval",
        TopLevel::TLExpr(..) => "expr",
        TopLevel::TLPublic(_) => unreachable!(),
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
        TopLevel::TLTheorem(_, prop, _, _) | TopLevel::TLCheck(_, prop, _) => {
            Some(Constraint::from_term(prop).display)
        }
        TopLevel::TLUse(..) | TopLevel::TLMod(..) | TopLevel::TLEval(..) | TopLevel::TLExpr(..) => {
            None
        }
        TopLevel::TLPublic(_) => unreachable!(),
    }
}

fn item_dependencies(top: &TopLevel<'_>) -> HashSet<String> {
    let mut names = HashSet::new();
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
        TopLevel::TLTheorem(_, prop, body, _) => {
            collect_term_names(prop, &mut names);
            collect_term_names(body, &mut names);
        }
        TopLevel::TLCheck(term, constraint, _) => {
            collect_term_names(term, &mut names);
            collect_term_names(constraint, &mut names);
        }
        TopLevel::TLEval(term, _) | TopLevel::TLExpr(term, _) => {
            collect_term_names(term, &mut names)
        }
        TopLevel::TLUse(..) | TopLevel::TLMod(..) => {}
        TopLevel::TLPublic(_) => unreachable!(),
    }
    if let Some(name) = item_name(top) {
        names.remove(&name);
    }
    names
}

fn collect_term_names(term: &Term<'_>, names: &mut HashSet<String>) {
    match term {
        Term::Named(name) | Term::Global(name) => {
            names.insert((*name).to_string());
        }
        Term::App(f, a) => {
            collect_term_names(f, names);
            collect_term_names(a, names);
        }
        Term::Lam(body)
        | Term::NamedLam(_, body)
        | Term::Unsafe(body)
        | Term::StructProj(body, _) => {
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
                    Tactic::Intro(_) => {}
                }
            }
        }
        Term::UnionDef(_, variants) => {
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
        TopLevel::TLUse(_, visibility, _)
            if matches!(visibility, ligare::front::parser::Visibility::Public) =>
        {
            item_name(top).into_iter().collect()
        }
        _ => Vec::new(),
    }
}

fn module_imports_for_top(top: &TopLevel<'_>) -> Vec<Vec<String>> {
    match unwrap_public(top) {
        TopLevel::TLUse(uses, _, _) => uses.iter().filter_map(use_tree_module).collect(),
        TopLevel::TLMod(name, _) => vec![vec![(*name).to_string()]],
        _ => Vec::new(),
    }
}

fn use_tree_module(tree: &UseTree<'_>) -> Option<Vec<String>> {
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
        other => other,
    }
}

fn stable_hash(value: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}
