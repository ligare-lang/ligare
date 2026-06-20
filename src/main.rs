use std::fs;

use bumpalo::Bump;
use clap::Parser;

use ligare::backend::zig::emit_zig;
use ligare::checker::TypeChecker;
use ligare::checker::context::empty_ctx;
use ligare::core::eval::Evaluator;
use ligare::core::pool::TermArena;
use ligare::core::syntax::Term;
use ligare::front::parser::{TopLevel, parse_expr_top, parse_program};
use ligare::pretty::PrettyPrinter;

#[derive(Parser)]
#[command(
    name = "ligare",
    about = "Ligare compiler frontend",
    long_about = "Each source file may contain:\n  def <name> [params] [: <type>] := <body>   top-level definition\n  #check <term> : <constraint>               type-check assertion\n  <expr>                                      evaluate expression"
)]
struct Cli {
    /// Evaluate an expression after processing all files
    #[arg(long, value_name = "EXPR")]
    eval: Option<String>,

    /// Emit Zig source code instead of evaluating
    #[arg(long)]
    emit_zig: bool,

    /// Source files to process
    #[arg(required = true)]
    files: Vec<String>,
}

/// The compiler orchestrator — owns the bump allocator, term arena, and
/// coordinates parsing, type checking, and evaluation.
///
/// This struct bundles all compilation state together instead of threading
/// it through free functions, following the OOP principle of encapsulation.
pub struct Compiler<'bump> {
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
    evaluator: Evaluator<'bump>,
    checker: TypeChecker<'bump>,
    /// Environment: maps top-level names to their defining terms.
    env: Vec<(&'bump str, &'bump Term<'bump>)>,
    /// Accumulated top-level items (for code generation).
    tops: Vec<TopLevel<'bump>>,
}

impl<'bump> Compiler<'bump> {
    pub fn new(bump: &'bump Bump, arena: &'bump TermArena<'bump>) -> Self {
        Self {
            bump,
            arena,
            evaluator: Evaluator::new(arena),
            checker: TypeChecker::new(arena),
            env: vec![],
            tops: vec![],
        }
    }

    /// Process a source file: parse it and handle each top-level item.
    pub fn process_file(&mut self, file: &str) -> Result<(), String> {
        let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
        let tops = parse_program(&content, self.bump, self.arena)
            .map_err(|e| format!("{}: parse error: {}", file, e))?;
        for top in tops {
            self.process_top_level(top)?;
        }
        Ok(())
    }

    /// Process a source file, collect top-level items, and type-check.
    /// Used by `--emit-zig` to ensure type errors are caught before
    /// code generation.
    pub fn collect_file(&mut self, file: &str) -> Result<(), String> {
        let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
        let tops = parse_program(&content, self.bump, self.arena)
            .map_err(|e| format!("{}: parse error: {}", file, e))?;
        // Type-check each item.  This catches errors like refinement
        // violations before emitting Zig.
        for top in &tops {
            self.process_top_level(top.clone())?;
        }
        self.tops.extend(tops);
        Ok(())
    }

    /// Evaluate an expression string (for `--eval`).
    pub fn eval_expr(&self, expr: &str) -> Result<(), String> {
        let term = parse_expr_top(expr, self.bump, self.arena)
            .map_err(|err| format!("--eval parse error: {}", err))?;
        let resolved = self.subst_top_level(term);
        match self.evaluator.eval(resolved) {
            Err(err) => Err(format!("--eval error: {}", err)),
            Ok(val) => {
                println!("{}", PrettyPrinter::pretty(val));
                Ok(())
            }
        }
    }

    /// Emit Zig code for all collected top-level items.
    pub fn emit_zig(&self) {
        println!("{}", emit_zig(&self.tops));
    }

    // ── private helpers ──

    /// Process a single top-level item.
    fn process_top_level(&mut self, top: TopLevel<'bump>) -> Result<(), String> {
        match top {
            TopLevel::TLDef(name, term) => match term {
                Term::Refine(_, parent, predicate) => {
                    println!("[refinement] {}", name);
                    self.checker.add_refinement(name, parent, predicate);
                }
                // parse_def always wraps the body in a Func node.
                // For zero-parameter definitions whose body is a
                // refinement, extract the Refine so it is properly
                // registered in the constraint table.
                Term::Func(_, params, _, _, _, body) if params.is_empty() => match body {
                    Term::Refine(_, parent, predicate) => {
                        println!("[refinement] {}", name);
                        self.checker.add_refinement(name, parent, predicate);
                    }
                    _ => {
                        println!("[defined] {}", name);
                        self.env.push((name, term));
                    }
                },
                _ => {
                    println!("[defined] {}", name);
                    self.env.push((name, term));
                }
            },
            TopLevel::TLCheck(term, constraint) => {
                let resolved = self.subst_top_level(term);
                let resolved_constraint = self.subst_top_level(constraint);
                match self
                    .checker
                    .check(&empty_ctx(), resolved, resolved_constraint)
                {
                    Err(err) => return Err(format!("check failed: {}", err)),
                    Ok(_) => println!("[OK]"),
                }
            }
            TopLevel::TLShow(term) => {
                let resolved = self.subst_top_level(term);
                match self.evaluator.eval(resolved) {
                    Err(err) => eprintln!("show error: {}", err),
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
            TopLevel::TLExpr(term) => {
                let resolved = self.subst_top_level(term);
                match self.evaluator.eval(resolved) {
                    Err(err) => eprintln!("eval error: {}", err),
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
        }
        Ok(())
    }

    /// Substitute known top-level definitions into a term.
    fn subst_top_level(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(term, &|t| {
            if let Term::Builtin(name) = t {
                self.env
                    .iter()
                    .find(|(n, _)| *n == *name)
                    .map(|(_, body)| *body)
            } else {
                None
            }
        })
    }
}

fn main() {
    let cli = Cli::parse();

    let bump = Bump::new();
    let arena = TermArena::new(&bump);

    // ── Zig code generation path ──
    if cli.emit_zig {
        let mut compiler = Compiler::new(&bump, &arena);
        let mut had_error = false;
        for file in &cli.files {
            if let Err(e) = compiler.collect_file(file) {
                eprintln!("{}", e);
                had_error = true;
            }
        }
        if !had_error {
            compiler.emit_zig();
        } else {
            std::process::exit(1);
        }
        return;
    }

    // ── Normal interpret / check / eval path ──
    let mut compiler = Compiler::new(&bump, &arena);
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
        std::process::exit(1);
    }
}
