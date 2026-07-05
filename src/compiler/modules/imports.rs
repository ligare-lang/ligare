use super::*;

pub(super) fn module_imports<'a, 'bump>(tops: &'a [TopLevel<'bump>]) -> Vec<ImportItem<'a, 'bump>> {
    tops.iter()
        .filter_map(|top| match unwrap_public(top).0 {
            TopLevel::TLUse(trees, visibility, _) => Some(ImportItem {
                trees,
                visibility: visibility.clone(),
            }),
            _ => None,
        })
        .collect()
}

pub(super) fn insert_import(
    imports: &mut HashMap<String, String>,
    local: String,
    target: String,
) -> Result<(), Diagnostic> {
    if let Some(existing) = imports.get(&local)
        && existing != &target
    {
        return Err(Diagnostic::new(format!(
            "duplicate import `{local}` from `{existing}` and `{target}`"
        )));
    }
    imports.insert(local, target);
    Ok(())
}

pub(super) fn import_deps<'bump>(
    current: &ModuleId,
    tops: &[TopLevel<'bump>],
    graph: &PackageModuleGraph,
) -> Result<Vec<ModuleId>, Diagnostic> {
    let mut deps = Vec::new();
    let mut seen = HashSet::new();
    if should_auto_import_std_prelude(current, graph) {
        let prelude = standard_prelude_module();
        if seen.insert(prelude.clone()) {
            deps.push(prelude);
        }
    }
    for import in module_imports(tops) {
        for tree in import.trees {
            if tree.path.len() < 2 && !tree.wildcard {
                return Err(Diagnostic::new("use path must include a module and symbol"));
            }
            let dep = if tree.wildcard {
                if is_namespace_wildcard_path(tree.path) {
                    current.namespace_import_prefix(tree.path, graph)?.0
                } else {
                    current.wildcard_module_import(tree.path, graph)?
                }
            } else if tree.path.len() >= 3 && is_namespace_segment(tree.path[tree.path.len() - 2]) {
                let parts = tree.path.to_vec();
                current.resolve_namespace_module_parts(&parts, 2, graph)?
            } else if tree.path.len() >= 2 && is_namespace_segment(tree.path[tree.path.len() - 1]) {
                let parts = tree.path.to_vec();
                current.resolve_namespace_module_parts(&parts, 1, graph)?
            } else {
                current.resolve_import_module(tree.path, graph)?
            };
            if seen.insert(dep.clone()) {
                deps.push(dep);
            }
        }
    }
    Ok(deps)
}

pub(super) fn qualified_term_deps<'bump>(
    current: &ModuleId,
    tops: &[TopLevel<'bump>],
    graph: &PackageModuleGraph,
) -> Result<Vec<ModuleId>, Diagnostic> {
    let mut deps = Vec::new();
    let mut seen = HashSet::new();
    let namespace_aliases = namespace_aliases_in_uses(tops);
    for name in qualified_names_in_tops(tops) {
        let Some(parts) = qualified_symbol_parts(&name) else {
            continue;
        };
        if namespace_aliases.contains(parts[0]) {
            continue;
        }
        let dep = current.resolve_import_module_parts(&parts, graph)?;
        if seen.insert(dep.clone()) {
            deps.push(dep);
        }
    }
    Ok(deps)
}

pub(super) fn qualified_term_names<'bump>(
    current: &ModuleId,
    tops: &[TopLevel<'bump>],
    graph: &PackageModuleGraph,
    exports: &HashMap<ModuleId, HashMap<String, String>>,
) -> Result<HashMap<String, String>, Diagnostic> {
    let mut resolved = HashMap::new();
    let namespace_aliases = namespace_aliases_in_uses(tops);
    for name in qualified_names_in_tops(tops) {
        let Some(parts) = qualified_symbol_parts(&name) else {
            continue;
        };
        if namespace_aliases.contains(parts[0]) {
            continue;
        }
        let requested = current
            .symbol_from_import_path_parts(&parts, graph)
            .ok_or_else(|| Diagnostic::new("qualified path must include a module and symbol"))?;
        let dep = current.resolve_import_module_parts(&parts, graph)?;
        let dep_exports = exports.get(&dep).ok_or_else(|| {
            Diagnostic::new(format!("module not found: {}", display_module(&dep)))
        })?;
        let Some(target) = dep_exports.get(&requested) else {
            if crate::config::is_std_internal_primitive_helper(&requested) {
                resolved.insert(name, requested);
                continue;
            }
            return Err(Diagnostic::new(format!(
                "cannot reference private or unknown symbol `{requested}`"
            )));
        };
        resolved.insert(name, target.clone());
    }
    Ok(resolved)
}

fn namespace_aliases_in_uses<'bump>(tops: &[TopLevel<'bump>]) -> HashSet<String> {
    let mut aliases = HashSet::new();
    for import in module_imports(tops) {
        for tree in import.trees {
            if !tree.wildcard
                && tree.path.len() >= 2
                && is_namespace_segment(tree.path[tree.path.len() - 1])
            {
                aliases.insert(
                    tree.alias
                        .map(|alias| alias.to_string())
                        .unwrap_or_else(|| tree.path[tree.path.len() - 1].to_string()),
                );
            }
        }
    }
    aliases
}

fn qualified_symbol_parts(name: &str) -> Option<Vec<&str>> {
    if !name.contains("::") {
        return None;
    }
    let parts = name.split("::").collect::<Vec<_>>();
    if parts.len() < 2 || parts.iter().any(|part| part.is_empty()) {
        None
    } else {
        Some(parts)
    }
}

pub(super) fn is_namespace_segment(name: &str) -> bool {
    name.chars()
        .next()
        .is_some_and(|ch| ch.is_ascii_uppercase())
}

pub(super) fn is_namespace_wildcard_path(path: &[Name<'_>]) -> bool {
    path.len() >= 2 && path.last().is_some_and(|name| is_namespace_segment(name))
}

fn qualified_names_in_tops<'bump>(tops: &[TopLevel<'bump>]) -> HashSet<String> {
    let mut names = HashSet::new();
    for top in tops {
        collect_qualified_names_from_top(top, &mut names);
    }
    names
}

fn collect_qualified_names_from_top<'bump>(top: &TopLevel<'bump>, names: &mut HashSet<String>) {
    let (top, _) = unwrap_public(top);
    match top {
        TopLevel::TLDef(_, params, ret, body, _) => {
            collect_qualified_names_from_params(params, names);
            if let Some(ret) = ret {
                collect_qualified_names_from_term(ret, names);
            }
            collect_qualified_names_from_term(body, names);
        }
        TopLevel::TLExternDef(_, params, ret, _) => {
            collect_qualified_names_from_params(params, names);
            collect_qualified_names_from_term(ret, names);
        }
        TopLevel::TLInstance(_, constraint, value, _) => {
            collect_qualified_names_from_term(constraint, names);
            collect_qualified_names_from_term(value, names);
        }
        TopLevel::TLVariable(params, _) => {
            collect_qualified_names_from_params(params, names);
        }
        TopLevel::TLTheorem(_, prop, body, _) | TopLevel::TLCheck(prop, body, _) => {
            collect_qualified_names_from_term(prop, names);
            collect_qualified_names_from_term(body, names);
        }
        TopLevel::TLEval(term, _) | TopLevel::TLExpr(term, _) | TopLevel::TLSplice(term, _) => {
            collect_qualified_names_from_term(term, names);
        }
        TopLevel::TLUse(..) | TopLevel::TLMod(..) | TopLevel::TLPublic(_) => {}
        TopLevel::TLAttributed(_, inner, _) => collect_qualified_names_from_top(inner, names),
        TopLevel::TLNamespace(_, items, _) => {
            for item in *items {
                collect_qualified_names_from_top(item, names);
            }
        }
    }
}

fn collect_qualified_names_from_params<'bump>(
    params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
    names: &mut HashSet<String>,
) {
    for (_, constraint) in params {
        if let Some(constraint) = constraint {
            collect_qualified_names_from_term(constraint, names);
        }
    }
}

fn collect_qualified_names_from_term<'bump>(term: &'bump Term<'bump>, names: &mut HashSet<String>) {
    match term {
        Term::Named(name) | Term::Global(name) => {
            if qualified_symbol_parts(name).is_some() {
                names.insert((*name).to_string());
            }
        }
        Term::App(f, a) => {
            collect_qualified_names_from_term(f, names);
            collect_qualified_names_from_term(a, names);
        }
        Term::Implicit(inner)
        | Term::Lam(inner)
        | Term::NamedLam(_, inner)
        | Term::Unsafe(inner)
        | Term::Pure(inner)
        | Term::Quote(inner)
        | Term::Splice(inner)
        | Term::StructProj(inner, _)
        | Term::MethodCall(inner, _) => collect_qualified_names_from_term(inner, names),
        Term::Pi(_, a, b) | Term::Refine(_, a, b) | Term::Annot(a, b) => {
            collect_qualified_names_from_term(a, names);
            collect_qualified_names_from_term(b, names);
        }
        Term::Let(_, val, body, constraint) => {
            collect_qualified_names_from_term(val, names);
            collect_qualified_names_from_term(body, names);
            if let Some(constraint) = constraint {
                collect_qualified_names_from_term(constraint, names);
            }
        }
        Term::IfThenElse(c, t, f) => {
            collect_qualified_names_from_term(c, names);
            collect_qualified_names_from_term(t, names);
            collect_qualified_names_from_term(f, names);
        }
        Term::ByProof(inner, tactics) => {
            if let Some(inner) = inner {
                collect_qualified_names_from_term(inner, names);
            }
            for tactic in tactics.iter() {
                match *tactic {
                    Tactic::Exact(term) | Tactic::Apply(term) | Tactic::Have(_, term) => {
                        collect_qualified_names_from_term(term, names);
                    }
                    Tactic::Intro(_) => {}
                    Tactic::Custom(_, args) => {
                        for arg in args {
                            collect_qualified_names_from_term(arg, names);
                        }
                    }
                }
            }
        }
        Term::EnumDef(_, variants) => {
            for (_, fields) in variants.iter() {
                for (_, constraint) in fields.iter() {
                    collect_qualified_names_from_term(constraint, names);
                }
            }
        }
        Term::Variant(_, _, values) | Term::StructCons(_, values) => {
            for value in values.iter() {
                collect_qualified_names_from_term(value, names);
            }
        }
        Term::NamedStructCons(name, fields) => {
            if let Some(name) = name
                && qualified_symbol_parts(name).is_some()
            {
                names.insert((*name).to_string());
            }
            for (_, value) in fields.iter() {
                collect_qualified_names_from_term(value, names);
            }
        }
        Term::Match(scrut, branches) => {
            collect_qualified_names_from_term(scrut, names);
            for (_, binds, body) in branches.iter() {
                for (_, constraint) in binds.iter() {
                    collect_qualified_names_from_term(constraint, names);
                }
                collect_qualified_names_from_term(body, names);
            }
        }
        Term::NamedMatch(scrut, branches) => {
            collect_qualified_names_from_term(scrut, names);
            for (_, binds, body) in branches.iter() {
                for (_, constraint) in binds.iter() {
                    collect_qualified_names_from_term(constraint, names);
                }
                collect_qualified_names_from_term(body, names);
            }
        }
        Term::Do(stmts) => {
            for stmt in stmts.iter() {
                match *stmt {
                    crate::core::syntax::DoStmt::Bind(_, rhs)
                    | crate::core::syntax::DoStmt::Expr(rhs) => {
                        collect_qualified_names_from_term(rhs, names);
                    }
                    crate::core::syntax::DoStmt::Let(_, rhs, constraint) => {
                        collect_qualified_names_from_term(rhs, names);
                        if let Some(constraint) = constraint {
                            collect_qualified_names_from_term(constraint, names);
                        }
                    }
                }
            }
        }
        Term::StructDef(_, fields) => {
            for (_, constraint) in fields.iter() {
                collect_qualified_names_from_term(constraint, names);
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

pub(super) fn declared_module_deps<'bump>(
    current: &ModuleId,
    tops: &[TopLevel<'bump>],
) -> Vec<ModuleId> {
    let mut deps = Vec::new();
    let mut seen = HashSet::new();
    for top in tops {
        let (top, _) = unwrap_public(top);
        if let TopLevel::TLMod(name, _) = top {
            let dep = current.child(name);
            if seen.insert(dep.clone()) {
                deps.push(dep);
            }
        }
    }
    deps
}

pub(super) fn declares_module<'bump>(tops: &[TopLevel<'bump>], name: &str) -> bool {
    tops.iter().any(|top| {
        let (top, _) = unwrap_public(top);
        matches!(top, TopLevel::TLMod(module_name, _) if *module_name == name)
    })
}

pub(super) fn declared_symbols<'bump>(
    tops: &[TopLevel<'bump>],
    module: &ModuleId,
    public_only: bool,
) -> HashMap<String, String> {
    let mut out = HashMap::new();
    collect_declared_symbols(tops, module, public_only, None, &mut out);
    out
}

pub(super) fn validate_namespace_conflicts<'bump>(
    tops: &[TopLevel<'bump>],
) -> Result<(), Diagnostic> {
    let mut seen: HashMap<(String, String, usize), std::ops::Range<usize>> = HashMap::new();
    for top in tops {
        let (top, _) = unwrap_public(top);
        let TopLevel::TLNamespace(namespace, items, _) = top else {
            continue;
        };
        for item in *items {
            let (item, public) = unwrap_public(item);
            if !public {
                continue;
            }
            if let TopLevel::TLDef(name, params, _, _, span)
            | TopLevel::TLExternDef(name, params, _, span) = item
            {
                let key = (namespace.to_string(), name.to_string(), params.len());
                if let Some(first) = seen.get(&key) {
                    return Err(Diagnostic::with_span(
                        format!(
                            "namespace `{}` has conflicting function `{}` with {} parameter(s); first declaration at {}..{}",
                            namespace,
                            name,
                            params.len(),
                            first.start,
                            first.end
                        ),
                        span.clone(),
                    ));
                }
                seen.insert(key, span.clone());
            }
        }
    }
    Ok(())
}

fn collect_declared_symbols<'bump>(
    tops: &[TopLevel<'bump>],
    module: &ModuleId,
    public_only: bool,
    namespace: Option<&str>,
    out: &mut HashMap<String, String>,
) {
    for top in tops {
        let (top, public) = unwrap_public(top);
        if public_only && !public && !matches!(top, TopLevel::TLNamespace(..)) {
            continue;
        }
        match top {
            TopLevel::TLDef(name, ..) | TopLevel::TLTheorem(name, ..) => {
                let logical = namespace
                    .map(|ns| format!("{ns}::{name}"))
                    .unwrap_or_else(|| name.to_string());
                let symbol = module.join_symbol(&logical);
                out.insert(symbol.clone(), symbol);
            }
            TopLevel::TLExternDef(name, ..) => {
                let logical = namespace
                    .map(|ns| format!("{ns}::{name}"))
                    .unwrap_or_else(|| name.to_string());
                let target = namespace
                    .map(|_| module.join_symbol(&logical))
                    .unwrap_or_else(|| name.to_string());
                out.insert(module.join_symbol(&logical), target);
            }
            TopLevel::TLNamespace(name, items, _) => {
                collect_declared_symbols(items, module, public_only, Some(name), out);
            }
            _ => {}
        }
    }
}

pub(super) fn has_public_main<'bump>(tops: &[TopLevel<'bump>]) -> bool {
    tops.iter().any(|top| {
        let (top, public) = unwrap_public(top);
        public && matches!(top, TopLevel::TLDef(name, ..) if *name == "main")
    })
}

pub(super) fn unwrap_public<'a, 'bump>(top: &'a TopLevel<'bump>) -> (&'a TopLevel<'bump>, bool) {
    let mut top = top;
    let mut public = false;
    loop {
        match top {
            TopLevel::TLPublic(inner) => {
                public = true;
                top = inner;
            }
            TopLevel::TLAttributed(_, inner, _) => top = inner,
            other => return (other, public),
        }
    }
}
