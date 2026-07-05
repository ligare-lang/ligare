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
use crate::document::{
    DiagnosticCheck, compiler_diagnostic_to_lsp, dedup_diagnostics, offset_to_position,
    parse_error_to_lsp,
};
use crate::navigation::SourceDocument;
use crate::semantic::semantic_tokens_for_source;
use crate::workspace::{
    ModuleKey, ProjectContext, fallback_file_candidates, fallback_imported_module_keys,
    fallback_module_key, project_context_for_uri, workspace_root_for_uris,
};
use crate::{ParseError, parse_program_lsp};

mod compiler_cache;
mod diagnostics;
mod parsing;
mod rewrite;
mod update;

use self::compiler_cache::{
    compiler_cache_is_fresh, resolve_module_imports, resolve_module_imports_from_index,
    update_compiler_cache,
};
use self::diagnostics::check_dirty_items;
use self::parsing::{
    changed_names, dirty_indices, merge_item_cache, module_imports_for_top, parse_file,
    stable_hash, unwrap_public, use_tree_module,
};
use self::rewrite::rewrite_top_for_module;

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
    export_targets: HashMap<String, String>,
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
    export_targets: HashMap<String, String>,
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

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FileCacheSummary {
    pub(crate) ast_items: usize,
    pub(crate) symbols: usize,
    pub(crate) exports: Vec<String>,
    pub(crate) items: usize,
}
