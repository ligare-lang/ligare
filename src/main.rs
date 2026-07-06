mod commands;

use std::path::PathBuf;
use std::process;

use bumpalo::Bump;
use clap::{Parser, Subcommand};

use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::package::{PackageType, UpdateMode};

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

    /// Emit backend source code instead of compiling it
    #[arg(long = "emit-source", alias = "emit-c")]
    emit_source: bool,

    /// Select the compiler backend
    #[arg(long, default_value = "c", value_name = "NAME")]
    backend: String,

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
    /// Initialize a Ligare package in an existing directory
    Init {
        /// Project directory
        #[arg(default_value = ".")]
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
    /// Generate Markdown documentation for Ligare source files
    Doc {
        /// File or directory to document
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Write Markdown output to a file instead of stdout
        #[arg(short = 'o', long, value_name = "PATH")]
        output: Option<PathBuf>,
        /// Include private items
        #[arg(long)]
        private: bool,
    },
}

fn main() {
    let cli = Cli::parse();

    if let Some(command) = &cli.command {
        match command {
            Command::New { path, lib, bin } => commands::run_new(path, *lib, *bin),
            Command::Init { path, lib, bin } => commands::run_init(path, *lib, *bin),
            Command::Build { path } => commands::run_build(path, &cli),
            Command::Update {
                name,
                version,
                path,
            } => commands::run_update(path, name.clone(), version.clone()),
            Command::Test { path } => commands::run_tests(path),
            Command::Fmt { path, check } => commands::run_fmt(path, *check),
            Command::Doc {
                path,
                output,
                private,
            } => commands::run_doc(path, output.as_deref(), *private),
        }
        return;
    }

    if cli.files.is_empty() {
        eprintln!(
            "ligare requires source files, or one of: new, init, build, update, test, fmt, doc"
        );
        process::exit(2);
    }

    let bump = Bump::new();
    let arena = TermArena::new(&bump);

    if cli.emit_source || cli.output.is_some() {
        commands::run_codegen(&cli, &bump, &arena);
    } else {
        commands::run_eval(&cli, &bump, &arena);
    }
}
