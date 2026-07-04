use super::*;

pub fn parse_module_surface(
    root: &Path,
    entry_path: &Path,
) -> Result<Vec<ParsedModuleSurface>, Diagnostic> {
    let module_root = entry_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_else(|| root.to_path_buf());
    parse_module_surface_at(&module_root, entry_path, Vec::new())
}

fn parse_module_surface_at(
    module_root: &Path,
    file: &Path,
    path: Vec<String>,
) -> Result<Vec<ParsedModuleSurface>, Diagnostic> {
    let file_str = file.to_string_lossy().into_owned();
    let source = read_source_file(&file_str)?;
    let bump = Bump::new();
    let arena = TermArena::new(&bump);
    let tops = parse_program(&source, &bump, &arena)
        .map_err(|e| Diagnostic::with_span(format!("parse error: {}", e.message), e.span))
        .map_err(|d| d.with_source(&file_str, &source))?;
    let mut surfaces = Vec::new();
    for top in &tops {
        let (top, public) = unwrap_public(top);
        let TopLevel::TLMod(name, _) = top else {
            continue;
        };
        let mut child_path = path.clone();
        child_path.push(name.to_string());
        let child_id = ModuleId {
            package: None,
            path: child_path.clone(),
        };
        let child_file = module_path(module_root, &child_id)?;
        if !child_file.exists() {
            return Err(Diagnostic::new(format!(
                "module not found: {} at {}",
                display_module(&child_id),
                child_file.display()
            )));
        }
        let children = parse_module_surface_at(module_root, &child_file, child_path.clone())?;
        surfaces.push(ParsedModuleSurface {
            path: child_path,
            public,
            children,
        });
    }
    Ok(surfaces)
}

pub fn public_module_paths(surface: &[ParsedModuleSurface]) -> HashSet<Vec<String>> {
    let mut paths = HashSet::new();
    for module in surface {
        collect_public_module_paths(module, true, &mut paths);
    }
    paths
}

fn collect_public_module_paths(
    module: &ParsedModuleSurface,
    parent_public: bool,
    paths: &mut HashSet<Vec<String>>,
) {
    let public = parent_public && module.public;
    if public {
        paths.insert(module.path.clone());
    }
    for child in &module.children {
        collect_public_module_paths(child, public, paths);
    }
}
