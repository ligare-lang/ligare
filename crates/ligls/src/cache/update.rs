use super::*;

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
        let project = self.project_context_for_cached_uri(&uri);
        let module_key = project
            .as_ref()
            .map(|project| project.module_key_for_uri(&uri))
            .unwrap_or_else(|| fallback_module_key(&uri));
        let parsed = parse_file(&uri, &text, &module_key, &bump, &arena);
        let semantic_top_ranges =
            crate::completion::expanded_top_level_ranges(&text, &parsed.ast, &bump, &arena);
        let semantic_tokens = semantic_tokens_for_source(&text, &parsed.ast, &semantic_top_ranges);
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
            super::diagnostics::DirtyCheckContext {
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
            export_targets: parsed.export_targets,
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
