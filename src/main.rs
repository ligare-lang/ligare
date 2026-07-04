use std::path::{Path, PathBuf};
use std::process;

use bumpalo::Bump;
use clap::{Parser, Subcommand};

use ligare::backend::c::{emit_c, emit_eval_c};
use ligare::backend::compile::{compile_and_run_c, compile_c};
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::format::format_source;
use ligare::package::{PackageType, UpdateMode, find_manifest_root, resolve_project, write_lock};

#[derive(Parser)]
#[command(
    name = "ligare",
    about = "Ligare compiler frontend",
    long_about = "Each source file may contain:\n  def <name> [params] [: <constraint>] := <body>   top-level definition\n  theorem <name> : <constraint> := <body>           named theorem/proof\n  #check <term> : <constraint>                     constraint assertion\n  <expr>                                            evaluate expression"
)]
struct Cli {
    #[command(subcommand)]
    command: Option<Command>,

    /// Evaluate an expression after processing all files
    #[arg(long, value_name = "EXPR")]
    eval: Option<String>,

    /// Emit C source code
    #[arg(long)]
    emit_c: bool,

    /// Compile and output a native executable
    #[arg(short = 'o', long, value_name = "PATH")]
    output: Option<PathBuf>,

    /// Source files to process
    files: Vec<String>,
}

#[derive(Subcommand)]
enum Command {
    /// Create a new Ligare package
    New {
        /// Package directory to create
        path: PathBuf,
        /// Create a library package
        #[arg(long, conflicts_with = "bin")]
        lib: bool,
        /// Create a binary package
        #[arg(long)]
        bin: bool,
    },
    /// Build the current Ligare package
    Build {
        /// Project directory
        #[arg(default_value = ".")]
        path: PathBuf,
    },
    /// Update dependencies and refresh ligare.lock
    Update {
        /// Dependency to update
        name: Option<String>,
        /// Version/tag/commit to pin for the dependency
        version: Option<String>,
        /// Project directory
        #[arg(short, long, default_value = ".")]
        path: PathBuf,
    },
    /// Run *_test.lig files in the current Ligare package
    Test {
        /// Project directory
        #[arg(default_value = ".")]
        path: PathBuf,
    },
    /// Format Ligare source files
    Fmt {
        /// File or directory to format
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Check whether formatting changes are needed
        #[arg(long)]
        check: bool,
    },
}

fn main() {
    let cli = Cli::parse();

    if let Some(command) = &cli.command {
        match command {
            Command::New { path, lib, bin } => run_new(path, *lib, *bin),
            Command::Build { path } => run_build(path, &cli),
            Command::Update {
                name,
                version,
                path,
            } => run_update(path, name.clone(), version.clone()),
            Command::Test { path } => run_tests(path),
            Command::Fmt { path, check } => run_fmt(path, *check),
        }
        return;
    }

    if cli.files.is_empty() {
        eprintln!("ligare requires source files, or one of: build, update, test");
        process::exit(2);
    }

    let bump = Bump::new();
    let arena = TermArena::new(&bump);

    if cli.emit_c || cli.output.is_some() {
        run_codegen(&cli, &bump, &arena);
    } else {
        run_eval(&cli, &bump, &arena);
    }
}

fn run_new(path: &Path, lib: bool, _bin: bool) {
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

fn run_build(path: &Path, cli: &Cli) {
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
            build_library_output_path(&root, &project.manifest.name, cli).as_deref(),
        ),
        PackageType::Binary => {
            let output = build_binary_output_path(&root, &project.manifest.name, cli);
            emit_or_compile_to(&compiler, output.as_deref());
        }
    }
}

fn run_update(path: &Path, name: Option<String>, version: Option<String>) {
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

fn run_tests(path: &Path) {
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

fn run_fmt(path: &Path, check: bool) {
    let files = match collect_format_targets(path) {
        Ok(files) => files,
        Err(e) => {
            eprintln!("{e}");
            process::exit(1);
        }
    };
    if files.is_empty() {
        eprintln!("no .lig files found under `{}`", path.display());
        process::exit(1);
    }

    let mut changed = Vec::new();
    let mut had_error = false;

    for file in files {
        let source = match std::fs::read_to_string(&file) {
            Ok(source) => source,
            Err(err) => {
                eprintln!("cannot read `{}`: {err}", file.display());
                had_error = true;
                continue;
            }
        };
        let formatted = match format_source(&source) {
            Ok(formatted) => formatted,
            Err(err) => {
                eprintln!("{}: {}", file.display(), err);
                had_error = true;
                continue;
            }
        };
        if source == formatted {
            continue;
        }
        changed.push(file.clone());
        if check {
            continue;
        }
        if let Err(err) = std::fs::write(&file, formatted) {
            eprintln!("cannot write `{}`: {err}", file.display());
            had_error = true;
        }
    }

    if check && !changed.is_empty() {
        for file in &changed {
            eprintln!("needs formatting: {}", file.display());
        }
        process::exit(1);
    }

    if had_error {
        process::exit(1);
    }
}

fn collect_format_targets(path: &Path) -> Result<Vec<PathBuf>, std::io::Error> {
    fn visit(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), std::io::Error> {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                let skip = path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| matches!(name, ".git" | "target"));
                if !skip {
                    visit(&path, out)?;
                }
                continue;
            }
            if path.extension().and_then(|ext| ext.to_str()) == Some("lig") {
                out.push(path);
            }
        }
        Ok(())
    }

    let mut files = Vec::new();
    if path.is_file() {
        files.push(path.to_path_buf());
    } else {
        visit(path, &mut files)?;
    }
    files.sort();
    Ok(files)
}

fn emit_or_compile(compiler: &Compiler<'_>, cli: &Cli) {
    emit_or_compile_to(compiler, cli.output.as_deref());
}

fn emit_or_compile_to(compiler: &Compiler<'_>, output: Option<&Path>) {
    let codegen = compiler.codegen_input();
    if output.is_some() {
        let eval_source = match emit_eval_c(
            codegen.tops,
            codegen.raw_defs,
            codegen.fun_sigs,
            codegen.enum_types,
            codegen.struct_types,
        ) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Eval code generation error: {e}");
                process::exit(1);
            }
        };
        if let Some(eval_source) = eval_source {
            match compile_and_run_c(&eval_source) {
                Ok(stdout) => print!("{stdout}"),
                Err(e) => {
                    eprintln!("Eval compilation error: {e}");
                    process::exit(1);
                }
            }
        }
    }
    let c_source = match emit_c(
        codegen.tops,
        codegen.raw_defs,
        codegen.fun_sigs,
        codegen.enum_types,
        codegen.struct_types,
    ) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Code generation error: {e}");
            process::exit(1);
        }
    };
    if output.is_none() {
        print!("{c_source}");
        return;
    }
    let output = output.unwrap();
    match compile_c(&c_source, output) {
        Ok(actual) => eprintln!("Compiled → {}", actual.display()),
        Err(e) => {
            eprintln!("Compilation error: {e}");
            process::exit(1);
        }
    }
}

fn emit_library_to(compiler: &Compiler<'_>, output: Option<&Path>) {
    let codegen = compiler.codegen_input();
    let c_source = match emit_c(
        codegen.tops,
        codegen.raw_defs,
        codegen.fun_sigs,
        codegen.enum_types,
        codegen.struct_types,
    ) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Code generation error: {e}");
            process::exit(1);
        }
    };
    let Some(output) = output else {
        print!("{c_source}");
        return;
    };
    if let Some(parent) = output.parent()
        && let Err(e) = std::fs::create_dir_all(parent)
    {
        eprintln!("cannot create output directory `{}`: {e}", parent.display());
        process::exit(1);
    }
    if let Err(e) = std::fs::write(output, c_source) {
        eprintln!("cannot write `{}`: {e}", output.display());
        process::exit(1);
    }
    eprintln!("Wrote {}", output.display());
}

fn build_binary_output_path(root: &Path, package_name: &str, cli: &Cli) -> Option<PathBuf> {
    if cli.emit_c {
        None
    } else {
        Some(
            cli.output
                .clone()
                .unwrap_or_else(|| root.join("target").join(package_binary_name(package_name))),
        )
    }
}

fn build_library_output_path(root: &Path, package_name: &str, cli: &Cli) -> Option<PathBuf> {
    if cli.emit_c {
        None
    } else {
        Some(
            cli.output
                .clone()
                .unwrap_or_else(|| root.join("target").join(format!("{package_name}.c"))),
        )
    }
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

fn find_tests(root: &std::path::Path) -> Result<Vec<PathBuf>, std::io::Error> {
    fn visit(dir: &std::path::Path, out: &mut Vec<PathBuf>) -> Result<(), std::io::Error> {
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

/// Code generation + optional native compilation.
fn run_codegen(cli: &Cli, bump: &Bump, arena: &TermArena<'_>) {
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

/// Normal interpret / check / eval path.
fn run_eval(cli: &Cli, bump: &Bump, arena: &TermArena<'_>) {
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
