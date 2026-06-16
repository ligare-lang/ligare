use std::fs;

use bumpalo::Bump;
use clap::Parser;

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
}

impl<'bump> Compiler<'bump> {
    pub fn new(bump: &'bump Bump, arena: &'bump TermArena<'bump>) -> Self {
        Self {
            bump,
            arena,
            evaluator: Evaluator::new(arena),
            checker: TypeChecker::new(arena),
            env: vec![],
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

    // ── private helpers ──

    /// Process a single top-level item.
    fn process_top_level(&mut self, top: TopLevel<'bump>) -> Result<(), String> {
        match top {
            TopLevel::TLDef(name, term) => match term {
                Term::Refine(_, parent, predicate) => {
                    println!("[refinement] {}", name);
                    self.checker.add_refinement(name, parent, predicate);
                }
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
                    Err(err) => eprintln!("check failed: {}", err),
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
        match term {
            Term::Builtin(name) => {
                if let Some((_, body)) = self.env.iter().find(|(n, _)| *n == *name) {
                    body
                } else {
                    term
                }
            }
            Term::App(f, a) => {
                let f2 = self.subst_top_level(f);
                let a2 = self.subst_top_level(a);
                self.arena.app(f2, a2)
            }
            Term::Lam(body) => {
                let b2 = self.subst_top_level(body);
                self.arena.lam(b2)
            }
            Term::Pi(n, a, b) => {
                let a2 = self.subst_top_level(a);
                let b2 = self.subst_top_level(b);
                self.arena.pi(n, a2, b2)
            }
            Term::Let(n, v, b, mc) => {
                let v2 = self.subst_top_level(v);
                let b2 = self.subst_top_level(b);
                let mc2 = mc.map(|c| self.subst_top_level(c));
                self.arena.let_(n, v2, b2, mc2)
            }
            Term::IfThenElse(c, t, f) => {
                let c2 = self.subst_top_level(c);
                let t2 = self.subst_top_level(t);
                let f2 = self.subst_top_level(f);
                self.arena.if_then_else(c2, t2, f2)
            }
            Term::Annot(t, c) => {
                let t2 = self.subst_top_level(t);
                let c2 = self.subst_top_level(c);
                self.arena.annot(t2, c2)
            }
            Term::ByProof(t, p) => {
                let t2 = self.subst_top_level(t);
                let p2 = self.subst_top_level(p);
                self.arena.by_proof(t2, p2)
            }
            Term::Refine(n, par, p) => {
                let par2 = self.subst_top_level(par);
                let p2 = self.subst_top_level(p);
                self.arena.refine(n, par2, p2)
            }
            Term::ProofBlock(t) => {
                let t2 = self.subst_top_level(t);
                self.arena.proof_block(t2)
            }
            // Leaf nodes
            _ => term,
        }
    }
}

fn main() {
    let cli = Cli::parse();

    let bump = Bump::new();
    let arena = TermArena::new(&bump);

    let mut compiler = Compiler::new(&bump, &arena);

    for file in &cli.files {
        if let Err(e) = compiler.process_file(file) {
            eprintln!("{}", e);
        }
    }

    if let Some(expr) = &cli.eval
        && let Err(e) = compiler.eval_expr(expr)
    {
        eprintln!("{}", e);
    }
}
