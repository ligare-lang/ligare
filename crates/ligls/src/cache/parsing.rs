use super::*;

pub(super) fn parse_file<'bump>(
    uri: &lsp::Url,
    text: &str,
    module_key: &ModuleKey,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> ParsedFile<'bump> {
    let (ast, parse_errors) = parse_program_lsp(text, bump, arena);
    let top_ranges = top_level_ranges(text, &ast);
    let mut module_imports = Vec::new();
    let mut symbols = Vec::new();
    let mut exports = Vec::new();
    let mut export_targets = HashMap::new();
    let mut item_infos = Vec::new();

    for (idx, (start, end, top)) in top_ranges.iter().enumerate() {
        let source = text.get(*start..*end).unwrap_or_default();
        let mut top_symbols = Vec::<Symbol>::new();
        collect_top_level_symbols(top, &mut top_symbols);
        symbols.extend(top_symbols.iter().map(|symbol| symbol.name.clone()));
        exports.extend(exported_names(top));
        export_targets.extend(exported_targets(top, module_key));
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
        export_targets,
    }
}

pub(super) fn changed_names(previous: Option<&FileCache>, current: &[ItemInfo]) -> HashSet<String> {
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

pub(super) fn dirty_indices(
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

pub(super) fn merge_item_cache(
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
        Term::NamedStructCons(name, fields) => {
            if let Some(name) = name {
                names.insert((*name).to_string());
            }
            for (_, value) in *fields {
                collect_term_names(value, names);
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

fn exported_targets(top: &TopLevel<'_>, module: &ModuleKey) -> HashMap<String, String> {
    let mut targets = HashMap::new();
    collect_exported_targets(top, module, None, false, &mut targets);
    targets
}

fn collect_exported_targets(
    top: &TopLevel<'_>,
    module: &ModuleKey,
    namespace: Option<&str>,
    public: bool,
    targets: &mut HashMap<String, String>,
) {
    match top {
        TopLevel::TLPublic(inner) => {
            collect_exported_targets(inner, module, namespace, true, targets);
        }
        TopLevel::TLAttributed(_, inner, _) => {
            collect_exported_targets(inner, module, namespace, public, targets);
        }
        TopLevel::TLDef(name, ..) | TopLevel::TLTheorem(name, ..) if public => {
            let local = namespace
                .map(|namespace| format!("{namespace}::{name}"))
                .unwrap_or_else(|| (*name).to_string());
            targets.insert(local.clone(), module.join_symbol(&local));
        }
        TopLevel::TLExternDef(name, ..) if public => {
            let local = namespace
                .map(|namespace| format!("{namespace}::{name}"))
                .unwrap_or_else(|| (*name).to_string());
            let target = namespace
                .map(|_| module.join_symbol(&local))
                .unwrap_or_else(|| (*name).to_string());
            targets.insert(local, target);
        }
        TopLevel::TLUse(uses, ligare::front::parser::Visibility::Public, _) => {
            for tree in *uses {
                let Some(local) = tree.alias.or_else(|| tree.path.last().copied()) else {
                    continue;
                };
                targets.insert(local.to_string(), module.join_symbol(local));
            }
        }
        TopLevel::TLNamespace(name, items, _) => {
            for item in *items {
                collect_exported_targets(item, module, Some(name), public, targets);
            }
        }
        _ => {}
    }
}

pub(super) fn module_imports_for_top(top: &TopLevel<'_>) -> Vec<Vec<String>> {
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

pub(super) fn use_tree_module(tree: &UseTree<'_>) -> Option<Vec<String>> {
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

pub(super) fn unwrap_public<'a, 'bump>(top: &'a TopLevel<'bump>) -> &'a TopLevel<'bump> {
    match top {
        TopLevel::TLPublic(inner) => unwrap_public(inner),
        TopLevel::TLAttributed(_, inner, _) => unwrap_public(inner),
        other => other,
    }
}

pub(super) fn stable_hash(value: &str) -> u64 {
    source_hash(value)
}
