use super::{Cli, Compiler, PackageType, UpdateMode};
use bumpalo::Bump;
use ligare::backend::Backend;
use ligare::core::pool::TermArena;
use ligare::package::{find_manifest_root, resolve_project, write_lock};
use ligare_doc as docgen;
use ligare_fmt as fmt;
use std::path::{Path, PathBuf};
use std::process;

pub(super) fn run_new(path: &Path, lib: bool, _bin: bool) {
    let package_type = if lib {
        PackageType::Lib
    } else {
        PackageType::Binary
    };
    if let Err(e) = create_package(path, package_type) {
        eprintln!("{e}");
        process::exit(1);
    }
}

fn create_package(path: &Path, package_type: PackageType) -> Result<(), String> {
    if path.exists() {
        if !path.is_dir() {
            return Err(format!(
                "`{}` already exists and is not a directory",
                path.display()
            ));
        }
        let mut entries = std::fs::read_dir(path)
            .map_err(|e| format!("cannot read `{}`: {e}", path.display()))?;
        if entries.next().is_some() {
            return Err(format!(
                "`{}` already exists and is not empty; use an empty directory",
                path.display()
            ));
        }
    } else {
        std::fs::create_dir_all(path)
            .map_err(|e| format!("cannot create `{}`: {e}", path.display()))?;
    }

    let name = package_name_from_path(path)?;
    let src = path.join("src");
    std::fs::create_dir_all(&src).map_err(|e| format!("cannot create `{}`: {e}", src.display()))?;

    let manifest = package_manifest(&name, package_type);
    write_new_file(&path.join("ligare.toml"), &manifest)?;

    let (entry_name, entry_source) = package_entry(package_type);
    write_new_file(&src.join(entry_name), entry_source)?;

    eprintln!(
        "Created {} package `{}`",
        package_kind(package_type),
        path.display()
    );
    Ok(())
}

fn package_name_from_path(path: &Path) -> Result<String, String> {
    let raw = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("cannot infer package name from `{}`", path.display()))?;
    let mut name = String::new();
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            name.push(ch);
        } else {
            name.push('_');
        }
    }
    if name
        .chars()
        .next()
        .is_none_or(|ch| !ch.is_ascii_alphabetic() && ch != '_')
    {
        name.insert(0, '_');
    }
    if name.chars().all(|ch| ch == '_') {
        return Err(format!(
            "cannot infer a valid package name from `{}`",
            path.display()
        ));
    }
    if is_ligare_keyword(&name) {
        name.push('_');
    }
    Ok(name)
}

fn is_ligare_keyword(name: &str) -> bool {
    matches!(
        name,
        "as" | "auto"
            | "by"
            | "def"
            | "do"
            | "else"
            | "enum"
            | "exact"
            | "extern"
            | "false"
            | "func"
            | "fun"
            | "have"
            | "if"
            | "in"
            | "instance"
            | "intro"
            | "let"
            | "match"
            | "mod"
            | "namespace"
            | "of"
            | "pub"
            | "pure"
            | "struct"
            | "then"
            | "theorem"
            | "true"
            | "unsafe"
            | "use"
            | "variable"
            | "where"
            | "with"
    )
}

fn package_manifest(name: &str, package_type: PackageType) -> String {
    match package_type {
        PackageType::Binary => format!(
            "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\ntype = \"binary\"\n\n[dependencies]\n"
        ),
        PackageType::Lib => format!(
            "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\ntype = \"lib\"\nentry = \"src/lib.lig\"\n\n[dependencies]\n"
        ),
    }
}

fn package_entry(package_type: PackageType) -> (&'static str, &'static str) {
    match package_type {
        PackageType::Binary => ("main.lig", "pub def main : IO () := ()\n"),
        PackageType::Lib => ("lib.lig", "pub def hello : str := \"hello\"\n"),
    }
}

fn package_kind(package_type: PackageType) -> &'static str {
    match package_type {
        PackageType::Binary => "binary",
        PackageType::Lib => "library",
    }
}

fn write_new_file(path: &Path, content: &str) -> Result<(), String> {
    if path.exists() {
        return Err(format!("`{}` already exists", path.display()));
    }
    std::fs::write(path, content).map_err(|e| format!("cannot write `{}`: {e}", path.display()))
}

pub(super) fn run_build(path: &Path, cli: &Cli) {
    let backend = backend_for(&cli.backend);
    let root = project_root_or_exit(path);
    let project = match resolve_project(&root, UpdateMode::Locked) {
        Ok(project) => project,
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1);
        }
    };
    if let Err(e) = write_lock(&root, &project.lock) {
        eprintln!("{}", e);
        process::exit(1);
    }
    let bump = Bump::new();
    let arena = TermArena::new(&bump);
    let mut compiler = Compiler::new(&bump, &arena);
    let entry = root.join(&project.manifest.entry);
    let result = match project.manifest.package_type {
        PackageType::Lib => compiler.collect_project_lib_entry(&root, &entry, project.graph),
        PackageType::Binary => compiler.collect_project_entry(&root, &entry, project.graph),
    };
    if let Err(e) = result {
        eprintln!("{}", e);
        process::exit(1);
    }
    match project.manifest.package_type {
        PackageType::Lib => emit_library_to(
            &compiler,
            build_library_output_path(&root, &project.manifest.name, cli, backend).as_deref(),
            backend,
        ),
        PackageType::Binary => {
            let output = build_binary_output_path(&root, &project.manifest.name, cli);
            emit_or_compile_to(&compiler, output.as_deref(), cli.emit_source, backend);
        }
    }
}

pub(super) fn run_update(path: &Path, name: Option<String>, version: Option<String>) {
    let root = project_root_or_exit(path);
    let mode = match (name, version) {
        (Some(name), Some(version)) => UpdateMode::Version { name, version },
        (Some(_), None) => {
            eprintln!("ligare update <name> requires a version");
            process::exit(1);
        }
        (None, Some(_)) => {
            eprintln!("ligare update version requires a dependency name");
            process::exit(1);
        }
        (None, None) => UpdateMode::Latest,
    };
    let project = match resolve_project(&root, mode) {
        Ok(project) => project,
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1);
        }
    };
    if let Err(e) = write_lock(&root, &project.lock) {
        eprintln!("{}", e);
        process::exit(1);
    }
}

pub(super) fn run_tests(path: &Path) {
    let root = project_root_or_exit(path);
    let tests = match find_tests(&root) {
        Ok(tests) => tests,
        Err(e) => {
            eprintln!("{e}");
            process::exit(1);
        }
    };
    let mut had_error = false;
    for test in tests {
        let project = match resolve_project(&root, UpdateMode::Locked) {
            Ok(project) => project,
            Err(e) => {
                eprintln!("{}", e);
                process::exit(1);
            }
        };
        let bump = Bump::new();
        let arena = TermArena::new(&bump);
        let mut compiler = Compiler::new(&bump, &arena);
        if let Err(e) = compiler.process_project_entry(&root, &test, project.graph) {
            eprintln!("{}", e);
            had_error = true;
        }
    }
    if had_error {
        process::exit(1);
    }
}

pub(super) fn run_fmt(path: &Path, check: bool) {
    let report = match fmt::format_path(path, check) {
        Ok(report) => report,
        Err(e) => {
            eprintln!("{e}");
            process::exit(1);
        }
    };

    if check && !report.changed.is_empty() {
        for file in &report.changed {
            eprintln!("needs formatting: {}", file.display());
        }
        process::exit(1);
    }
}

pub(super) fn run_doc(path: &Path, output: Option<&Path>, include_private: bool) {
    let markdown = match docgen::generate_markdown(path, &docgen::DocOptions { include_private }) {
        Ok(markdown) => markdown,
        Err(err) => {
            eprintln!("{err}");
            process::exit(1);
        }
    };
    if let Some(output) = output {
        if let Err(err) = std::fs::write(output, &markdown) {
            eprintln!("cannot write `{}`: {err}", output.display());
            process::exit(1);
        }
    } else {
        print!("{markdown}");
    }
}

fn emit_or_compile(compiler: &Compiler<'_>, cli: &Cli) {
    emit_or_compile_to(
        compiler,
        cli.output.as_deref(),
        cli.emit_source,
        backend_for(&cli.backend),
    );
}

fn emit_or_compile_to(
    compiler: &Compiler<'_>,
    output: Option<&Path>,
    emit_source: bool,
    backend: &'static dyn Backend,
) {
    let codegen = compiler.codegen_input();
    if emit_source {
        let source = match backend.emit_source(codegen) {
            Ok(source) => source,
            Err(e) => {
                eprintln!("Code generation error: {e}");
                process::exit(1);
            }
        };
        if let Some(output) = output {
            if let Some(parent) = output.parent()
                && let Err(e) = std::fs::create_dir_all(parent)
            {
                eprintln!("cannot create output directory `{}`: {e}", parent.display());
                process::exit(1);
            }
            if let Err(e) = std::fs::write(output, source) {
                eprintln!("cannot write `{}`: {e}", output.display());
                process::exit(1);
            }
            eprintln!("Wrote {}", output.display());
        } else {
            print!("{source}");
        }
        return;
    }

    let eval_source = match backend.emit_eval_source(codegen) {
        Ok(source) => source,
        Err(e) => {
            eprintln!("Eval code generation error: {e}");
            process::exit(1);
        }
    };
    if let Some(eval_source) = eval_source {
        match backend.run_eval_source(&eval_source) {
            Ok(stdout) => print!("{stdout}"),
            Err(e) => {
                eprintln!("Eval compilation error: {e}");
                process::exit(1);
            }
        }
    }
    let source = match backend.emit_source(codegen) {
        Ok(source) => source,
        Err(e) => {
            eprintln!("Code generation error: {e}");
            process::exit(1);
        }
    };
    let Some(output) = output else {
        print!("{source}");
        return;
    };
    match backend.compile_source(&source, output) {
        Ok(actual) => eprintln!("Compiled → {}", actual.display()),
        Err(e) => {
            eprintln!("Compilation error: {e}");
            process::exit(1);
        }
    }
}

fn emit_library_to(compiler: &Compiler<'_>, output: Option<&Path>, backend: &'static dyn Backend) {
    let codegen = compiler.codegen_input();
    let source = match backend.emit_source(codegen) {
        Ok(source) => source,
        Err(e) => {
            eprintln!("Code generation error: {e}");
            process::exit(1);
        }
    };
    let Some(output) = output else {
        print!("{source}");
        return;
    };
    if let Some(parent) = output.parent()
        && let Err(e) = std::fs::create_dir_all(parent)
    {
        eprintln!("cannot create output directory `{}`: {e}", parent.display());
        process::exit(1);
    }
    if let Err(e) = std::fs::write(output, source) {
        eprintln!("cannot write `{}`: {e}", output.display());
        process::exit(1);
    }
    eprintln!("Wrote {}", output.display());
}

fn build_binary_output_path(root: &Path, package_name: &str, cli: &Cli) -> Option<PathBuf> {
    if cli.emit_source {
        cli.output.clone()
    } else {
        Some(
            cli.output
                .clone()
                .unwrap_or_else(|| root.join("target").join(package_binary_name(package_name))),
        )
    }
}

fn build_library_output_path(
    root: &Path,
    package_name: &str,
    cli: &Cli,
    backend: &'static dyn Backend,
) -> Option<PathBuf> {
    if cli.emit_source {
        cli.output.clone()
    } else {
        Some(cli.output.clone().unwrap_or_else(|| {
            root.join("target")
                .join(format!("{package_name}.{}", backend.source_extension()))
        }))
    }
}

fn backend_for(name: &str) -> &'static dyn Backend {
    if let Some(backend) = ligare::backend::backend_named(name) {
        return backend;
    }
    let available = ligare::backend::registry()
        .names()
        .collect::<Vec<_>>()
        .join(", ");
    eprintln!("unknown backend `{name}`; available backends: {available}");
    process::exit(2);
}

fn package_binary_name(package_name: &str) -> String {
    let name: String = package_name
        .chars()
        .map(|ch| match ch {
            '/' | '\\' => '_',
            ch => ch,
        })
        .collect();
    if name.is_empty() {
        "main".to_string()
    } else {
        name
    }
}

fn project_root_or_exit(path: &Path) -> PathBuf {
    match find_manifest_root(path) {
        Ok(root) => root,
        Err(e) => {
            eprintln!("{}", e);
            process::exit(1);
        }
    }
}

fn find_tests(root: &Path) -> Result<Vec<PathBuf>, std::io::Error> {
    fn visit(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), std::io::Error> {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().and_then(|n| n.to_str()) != Some(".git") {
                    visit(&path, out)?;
                }
            } else if path
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|name| name.ends_with("_test.lig"))
            {
                out.push(path);
            }
        }
        Ok(())
    }
    let mut tests = Vec::new();
    visit(root, &mut tests)?;
    tests.sort();
    Ok(tests)
}

pub(super) fn run_codegen(cli: &Cli, bump: &Bump, arena: &TermArena<'_>) {
    let mut compiler = Compiler::new(bump, arena);
    let mut had_error = false;

    for file in &cli.files {
        if let Err(e) = compiler.collect_file(file) {
            eprintln!("{}", e);
            had_error = true;
        }
    }
    if had_error {
        process::exit(1);
    }

    emit_or_compile(&compiler, cli);
}

pub(super) fn run_eval(cli: &Cli, bump: &Bump, arena: &TermArena<'_>) {
    let mut compiler = Compiler::new(bump, arena);
    let mut had_error = false;

    for file in &cli.files {
        if let Err(e) = compiler.process_file(file) {
            eprintln!("{}", e);
            had_error = true;
        }
    }

    if let Some(expr) = &cli.eval
        && let Err(e) = compiler.eval_expr(expr)
    {
        eprintln!("{}", e);
        had_error = true;
    }

    if had_error {
        process::exit(1);
    }
}
