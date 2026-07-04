use super::*;

impl<'bump> Compiler<'bump> {
    pub(crate) fn process_module_entry(&mut self, file: &str) -> Result<(), Diagnostic> {
        let env = self.load_module_graph(file)?;
        for id in env.order {
            let tops = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in tops {
                self.process_top_level(top)?;
            }
        }
        self.validate_module_main()?;
        let cache_root =
            package_root_for_file(Path::new(file)).unwrap_or_else(|| PathBuf::from("."));
        let root_package = root_cache_package_name(&cache_root);
        save_module_cache_records(&cache_root, &root_package, env.cache_records.into_values())
    }

    pub(crate) fn collect_module_entry(&mut self, file: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        let env = self.load_module_graph(file)?;
        let mut checked_records = Vec::new();
        for id in env.order {
            let content = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in &content {
                self.process_top_level(top.clone())?;
            }
            let codegen = self.collect_codegen_state(&content)?;
            let monomorphized = self.monomorphize_for_codegen(content, codegen)?;
            let eraser =
                crate::checker::erase::Eraser::new(self.arena, self.checker.builtins.clone());
            let erased = self.erase_and_collect_tops(monomorphized.tops, &eraser)?;
            self.extend_codegen_state(monomorphized.codegen);
            self.tops.extend(erased.tops);
            if let Some(record) = env.cache_records.get(&id) {
                checked_records.push(record.clone());
            }
        }
        self.validate_module_main()?;
        let cache_root =
            package_root_for_file(Path::new(file)).unwrap_or_else(|| PathBuf::from("."));
        let root_package = root_cache_package_name(&cache_root);
        save_module_cache_records(&cache_root, &root_package, checked_records)
    }

    pub fn process_project_entry(
        &mut self,
        root: &Path,
        entry: &Path,
        graph: PackageModuleGraph,
    ) -> Result<(), Diagnostic> {
        let env = self.load_project_module_graph(root, entry, graph, true)?;
        let mut checked_records = Vec::new();
        for id in env.order {
            let tops = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in tops {
                self.process_top_level(top)?;
            }
            if let Some(record) = env.cache_records.get(&id) {
                checked_records.push(record.clone());
            }
        }
        self.validate_module_main()?;
        let root_package = root_cache_package_name(root);
        save_module_cache_records(root, &root_package, checked_records)
    }

    pub fn collect_project_entry(
        &mut self,
        root: &Path,
        entry: &Path,
        graph: PackageModuleGraph,
    ) -> Result<(), Diagnostic> {
        self.quiet = true;
        let env = self.load_project_module_graph(root, entry, graph, true)?;
        let mut checked_records = Vec::new();
        for id in env.order {
            let content = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in &content {
                self.process_top_level(top.clone())?;
            }
            let codegen = self.collect_codegen_state(&content)?;
            let monomorphized = self.monomorphize_for_codegen(content, codegen)?;
            let eraser =
                crate::checker::erase::Eraser::new(self.arena, self.checker.builtins.clone());
            let erased = self.erase_and_collect_tops(monomorphized.tops, &eraser)?;
            self.extend_codegen_state(monomorphized.codegen);
            self.tops.extend(erased.tops);
            if let Some(record) = env.cache_records.get(&id) {
                checked_records.push(record.clone());
            }
        }
        self.validate_module_main()?;
        let root_package = root_cache_package_name(root);
        save_module_cache_records(root, &root_package, checked_records)
    }

    pub fn collect_project_lib_entry(
        &mut self,
        root: &Path,
        entry: &Path,
        graph: PackageModuleGraph,
    ) -> Result<(), Diagnostic> {
        self.quiet = true;
        let env = self.load_project_module_graph(root, entry, graph, false)?;
        let mut checked_records = Vec::new();
        for id in env.order {
            let content = env.rewritten.get(&id).cloned().unwrap_or_default();
            for top in &content {
                self.process_top_level(top.clone())?;
            }
            let codegen = self.collect_codegen_state(&content)?;
            let monomorphized = self.monomorphize_for_codegen(content, codegen)?;
            let eraser =
                crate::checker::erase::Eraser::new(self.arena, self.checker.builtins.clone());
            let erased = self.erase_and_collect_tops(monomorphized.tops, &eraser)?;
            self.extend_codegen_state(monomorphized.codegen);
            self.tops.extend(erased.tops);
            if let Some(record) = env.cache_records.get(&id) {
                checked_records.push(record.clone());
            }
        }
        let root_package = root_cache_package_name(root);
        save_module_cache_records(root, &root_package, checked_records)?;
        Ok(())
    }

    fn load_module_graph(&self, entry: &str) -> Result<ModuleEnv<'bump>, Diagnostic> {
        let entry_path = PathBuf::from(entry);
        let root = entry_path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from("."));
        self.load_project_module_graph(&root, &entry_path, PackageModuleGraph::default(), true)
    }

    fn extend_codegen_state(&mut self, codegen: crate::compiler::CodegenState<'bump>) {
        self.raw_defs.extend(codegen.raw_defs);
        extend_named_unique(&mut self.fun_sigs, codegen.fun_sigs);
        extend_named_unique(&mut self.enum_types, codegen.enum_types);
        extend_named_unique(&mut self.struct_types, codegen.struct_types);
    }

    fn load_project_module_graph(
        &self,
        root: &Path,
        entry_path: &Path,
        graph: PackageModuleGraph,
        require_main: bool,
    ) -> Result<ModuleEnv<'bump>, Diagnostic> {
        let module_root = entry_path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| root.to_path_buf());
        let mut parsed = HashMap::new();
        self.load_module_as(
            &module_root,
            entry_path.to_path_buf(),
            ModuleId::root(),
            &graph,
            &mut parsed,
        )?;
        let entry_id = ModuleId::root();
        let root_module = parsed
            .get(&entry_id)
            .ok_or_else(|| Diagnostic::new("entry module was not loaded"))?;
        if require_main && entry_id == ModuleId::root() && !has_public_main(&root_module.tops) {
            return Err(Diagnostic::new(format!(
                "entry module `{}` must define `pub main : IO ()`",
                entry_path.display()
            )));
        }
        let exports = self.collect_exports(&parsed, &graph)?;
        let cache_records = module_cache_records(&parsed, &exports);
        let mut env = ModuleEnv {
            exports,
            rewritten: HashMap::new(),
            cache_records,
            order: Vec::new(),
        };
        let mut visiting = Vec::new();
        let mut done = HashSet::new();
        let visit = ModuleVisitContext {
            root: &module_root,
            graph: &graph,
            parsed: &parsed,
        };
        self.visit_module(&entry_id, &visit, &mut env, &mut visiting, &mut done)?;
        Ok(env)
    }

    fn load_module_as(
        &self,
        root: &Path,
        file: PathBuf,
        id: ModuleId,
        graph: &PackageModuleGraph,
        parsed: &mut HashMap<ModuleId, ParsedModule<'bump>>,
    ) -> Result<ModuleId, Diagnostic> {
        if parsed.contains_key(&id) {
            return Ok(id);
        }
        let file_str = file.to_string_lossy().into_owned();
        let source = read_source_file(&file_str)?;
        let hash = source_hash(&source);
        let tops = parse_program(&source, self.bump, self.arena)
            .map_err(|e| Diagnostic::with_span(format!("parse error: {}", e.message), e.span))
            .map_err(|d| d.with_source(&file_str, &source))?;
        let imports = module_cache_imports(&id, &tops, graph)?;
        parsed.insert(
            id.clone(),
            ParsedModule {
                id: id.clone(),
                file: file.clone(),
                source_hash: hash,
                imports,
                tops: tops.clone(),
            },
        );
        if should_auto_import_std_prelude(&id, graph) {
            self.ensure_declared_module_loaded(root, &standard_prelude_module(), graph, parsed)?;
        }
        for module in declared_module_deps(&id, &tops) {
            self.ensure_declared_module_loaded(root, &module, graph, parsed)?;
        }
        for module in import_deps(&id, &tops, graph)? {
            self.ensure_declared_module_loaded(root, &module, graph, parsed)?;
        }
        for module in qualified_term_deps(&id, &tops, graph)? {
            self.ensure_declared_module_loaded(root, &module, graph, parsed)?;
        }
        Ok(id)
    }

    fn ensure_declared_module_loaded(
        &self,
        root: &Path,
        module: &ModuleId,
        graph: &PackageModuleGraph,
        parsed: &mut HashMap<ModuleId, ParsedModule<'bump>>,
    ) -> Result<(), Diagnostic> {
        if parsed.contains_key(module) {
            return Ok(());
        }

        if is_standard_library_module(module, graph) && !module.path.is_empty() {
            let (module_root, file) = module_file(root, module, graph)?;
            self.load_module_as(&module_root, file, module.clone(), graph, parsed)?;
            return Ok(());
        }

        if module.path == ["main"] {
            let (module_root, file) = module_file(root, module, graph)?;
            self.load_module_as(&module_root, file, module.clone(), graph, parsed)?;
            return Ok(());
        }

        let Some(parent) = module.parent() else {
            let (module_root, file) = module_file(root, module, graph)?;
            self.load_module_as(&module_root, file, module.clone(), graph, parsed)?;
            return Ok(());
        };
        self.ensure_declared_module_loaded(root, &parent, graph, parsed)?;
        let leaf = module
            .path
            .last()
            .ok_or_else(|| Diagnostic::new("module path cannot be empty"))?;
        let parent_module = parsed.get(&parent).ok_or_else(|| {
            Diagnostic::new(format!("module not found: {}", display_module(&parent)))
        })?;
        if !declares_module(&parent_module.tops, leaf) {
            return Err(Diagnostic::new(format!(
                "module `{}` is not declared by parent module `{}`",
                display_module(module),
                display_module(&parent)
            )));
        }
        let (module_root, file) = module_file(root, module, graph)?;
        self.load_module_as(&module_root, file, module.clone(), graph, parsed)
            .map(|_| ())
    }

    fn collect_exports(
        &self,
        parsed: &HashMap<ModuleId, ParsedModule<'bump>>,
        graph: &PackageModuleGraph,
    ) -> Result<HashMap<ModuleId, HashMap<String, String>>, Diagnostic> {
        let mut direct = HashMap::new();
        for (id, module) in parsed {
            validate_namespace_conflicts(&module.tops)?;
            direct.insert(id.clone(), declared_symbols(&module.tops, id, true));
        }
        let mut exports = direct.clone();
        let mut changed = true;
        while changed {
            changed = false;
            for (id, module) in parsed {
                let mut set = exports.get(id).cloned().unwrap_or_default();
                for import in module_imports(&module.tops) {
                    if import.visibility != Visibility::Public {
                        continue;
                    }
                    for tree in import.trees {
                        if tree.wildcard {
                            let dep = if is_namespace_wildcard_path(tree.path) {
                                module.id.namespace_import_prefix(tree.path, graph)?.0
                            } else {
                                module.id.wildcard_module_import(tree.path, graph)?
                            };
                            let dep_exports = exports.get(&dep).ok_or_else(|| {
                                Diagnostic::new(format!(
                                    "module not found: {}",
                                    display_module(&dep)
                                ))
                            })?;
                            if is_namespace_wildcard_path(tree.path) {
                                let (_, prefix) =
                                    module.id.namespace_import_prefix(tree.path, graph)?;
                                let prefix_with_sep = format!("{prefix}::");
                                for (exported, target) in dep_exports {
                                    let Some(local) = exported.strip_prefix(&prefix_with_sep)
                                    else {
                                        continue;
                                    };
                                    if local.contains("::") {
                                        continue;
                                    }
                                    let exported = id.join_symbol(local);
                                    if set.insert(exported, target.clone()).is_none() {
                                        changed = true;
                                    }
                                }
                            } else {
                                for (exported, target) in dep_exports {
                                    let local = dep.local_symbol_name(exported);
                                    let exported = id.join_symbol(&local);
                                    if set.insert(exported, target.clone()).is_none() {
                                        changed = true;
                                    }
                                }
                            }
                            continue;
                        }
                        let requested =
                            id.symbol_from_import_path(tree.path, graph)
                                .ok_or_else(|| {
                                    Diagnostic::new("pub use path must include a module and symbol")
                                })?;
                        let dep = id.resolve_import_module(tree.path, graph)?;
                        let dep_exports = exports.get(&dep).ok_or_else(|| {
                            Diagnostic::new(format!("module not found: {}", display_module(&dep)))
                        })?;
                        let Some(target) = dep_exports.get(&requested) else {
                            return Err(Diagnostic::new(format!(
                                "cannot re-export private or unknown symbol `{requested}`"
                            )));
                        };
                        let local = tree
                            .alias
                            .map(|a| a.to_string())
                            .unwrap_or_else(|| tree.path.last().unwrap().to_string());
                        let exported = id.join_symbol(&local);
                        if set.insert(exported, target.clone()).is_none() {
                            changed = true;
                        }
                    }
                }
                exports.insert(id.clone(), set);
            }
        }
        Ok(exports)
    }

    fn visit_module(
        &self,
        id: &ModuleId,
        visit: &ModuleVisitContext<'_, 'bump>,
        env: &mut ModuleEnv<'bump>,
        visiting: &mut Vec<ModuleId>,
        done: &mut HashSet<ModuleId>,
    ) -> Result<(), Diagnostic> {
        if done.contains(id) {
            return Ok(());
        }
        if let Some(pos) = visiting.iter().position(|m| m == id) {
            let mut cycle = visiting[pos..]
                .iter()
                .map(display_module)
                .collect::<Vec<_>>();
            cycle.push(display_module(id));
            return Err(Diagnostic::new(format!(
                "cyclic module dependency: {}",
                cycle.join(" -> ")
            )));
        }
        visiting.push(id.clone());
        let module = visit
            .parsed
            .get(id)
            .ok_or_else(|| Diagnostic::new(format!("module not found: {}", display_module(id))))?;
        for dep in declared_module_deps(id, &module.tops)
            .into_iter()
            .chain(import_deps(id, &module.tops, visit.graph)?)
            .chain(qualified_term_deps(id, &module.tops, visit.graph)?)
        {
            let (_dep_root, dep_file) = module_file(visit.root, &dep, visit.graph)?;
            if !visit.parsed.contains_key(&dep) || !dep_file.exists() {
                return Err(Diagnostic::new(format!(
                    "module not found: {} at {}",
                    display_module(&dep),
                    dep_file.display()
                )));
            }
            self.visit_module(&dep, visit, env, visiting, done)?;
        }
        visiting.pop();
        let rewritten = self.rewrite_module(module, &env.exports, visit.graph)?;
        env.rewritten.insert(id.clone(), rewritten);
        env.order.push(id.clone());
        done.insert(id.clone());
        Ok(())
    }

    fn validate_module_main(&self) -> Result<(), Diagnostic> {
        if !self.env.contains_key("main") {
            return Err(Diagnostic::new("entry module must define `main : IO ()`"));
        }
        Ok(())
    }
}

fn extend_named_unique<'a, T>(target: &mut Vec<(&'a str, T)>, source: Vec<(&'a str, T)>) {
    let mut seen = target
        .iter()
        .map(|(name, _)| name.to_string())
        .collect::<HashSet<_>>();
    for (name, value) in source {
        if seen.insert(name.to_string()) {
            target.push((name, value));
        }
    }
}
