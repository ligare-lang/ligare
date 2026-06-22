use std::path::PathBuf;
use std::process;

use bumpalo::Bump;
use clap::Parser;

use ligare::backend::c::emit_c;
use ligare::backend::compile::compile_c;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

#[derive(Parser)]
#[command(
    name = "ligare",
    about = "Ligare compiler frontend",
    long_about = "Each source file may contain:\n  def <name> [params] [: <type>] := <body>   top-level definition\n  theorem <name> : <type> := <body>           named theorem/proof\n  #check <term> : <constraint>               type-check assertion\n  <expr>                                      evaluate expression"
)]
struct Cli {
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
    #[arg(required = true)]
    files: Vec<String>,
}

fn main() {
    let cli = Cli::parse();

    let bump = Bump::new();
    let arena = TermArena::new(&bump);

    if cli.emit_c || cli.output.is_some() {
        run_codegen(&cli, &bump, &arena);
    } else {
        run_eval(&cli, &bump, &arena);
    }
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

    let c_source = emit_c(compiler.tops(), compiler.fun_sigs());

    // --emit-c: print C source
    if cli.output.is_none() {
        print!("{c_source}");
        return;
    }

    // -o <path>: compile to native binary.
    let output = cli.output.as_ref().unwrap();
    match compile_c(&c_source, output) {
        Ok(actual) => eprintln!("Compiled → {}", actual.display()),
        Err(e) => {
            eprintln!("Compilation error: {e}");
            process::exit(1);
        }
    }
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
