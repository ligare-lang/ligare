use std::path::{Path, PathBuf};
use std::process;

use bumpalo::Bump;
use clap::{Parser, Subcommand};

use ligare::backend::c::{emit_c, emit_eval_c};
use ligare::backend::compile::{compile_and_run_c, compile_c};
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::package::{UpdateMode, find_manifest_root, resolve_project, write_lock};

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
}

fn main() {
    let cli = Cli::parse();

    if let Some(command) = &cli.command {
        match command {
            Command::Build { path } => run_build(path, &cli),
            Command::Update {
                name,
                version,
                path,
            } => run_update(path, name.clone(), version.clone()),
            Command::Test { path } => run_tests(path),
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

fn run_build(path: &PathBuf, cli: &Cli) {
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
    let output = build_output_path(&root, &project.manifest.name, cli);
    let result = if cli.emit_c || output.is_some() {
        compiler.collect_project_entry(&root, &entry, project.graph)
    } else {
        compiler.process_project_entry(&root, &entry, project.graph)
    };
    if let Err(e) = result {
        eprintln!("{}", e);
        process::exit(1);
    }
    if cli.emit_c || output.is_some() {
        emit_or_compile_to(&compiler, output.as_deref());
    }
}

fn run_update(path: &PathBuf, name: Option<String>, version: Option<String>) {
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

fn run_tests(path: &PathBuf) {
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
            codegen.union_types,
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
        codegen.union_types,
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

fn build_output_path(root: &Path, package_name: &str, cli: &Cli) -> Option<PathBuf> {
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

fn project_root_or_exit(path: &PathBuf) -> PathBuf {
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
