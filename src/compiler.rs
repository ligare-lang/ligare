use std::fs;

use bumpalo::Bump;

use crate::checker::TypeChecker;
use crate::checker::context::empty_ctx;
use crate::core::erase::erase;
use crate::core::eval::Evaluator;
use crate::core::pool::TermArena;
use crate::core::syntax::Term;
use crate::front::parser::{TopLevel, parse_expr_top, parse_program};
use crate::pretty::PrettyPrinter;

/// The compiler orchestrator — owns the bump allocator, term arena, and
/// coordinates parsing, type checking, and evaluation.
///
/// This struct bundles all compilation state together instead of threading
/// it through free functions.
pub struct Compiler<'bump> {
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
    evaluator: Evaluator<'bump>,
    checker: TypeChecker<'bump>,
    /// Environment: maps top-level names to their defining terms.
    env: Vec<(&'bump str, &'bump Term<'bump>)>,
    /// Accumulated top-level items (for code generation).
    pub tops: Vec<TopLevel<'bump>>,
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
    pub fn collect_file(&mut self, file: &str) -> Result<(), String> {
        let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
        let tops = parse_program(&content, self.bump, self.arena)
            .map_err(|e| format!("{}: parse error: {}", file, e))?;
        for top in &tops {
            self.process_top_level(top.clone())?;
        }
        // Evaluate TLShow/TLExpr terms for codegen, then erase all
        // proof-irrelevant subterms (prop / theorem / proof universes)
        // so the C backend only sees pure data.
        let evald_tops: Vec<TopLevel<'bump>> = tops
            .into_iter()
            .map(|top| match top {
                TopLevel::TLShow(term) | TopLevel::TLExpr(term) => {
                    let resolved = self.subst_top_level(term);
                    match self.evaluator.eval(resolved) {
                        Ok(val) => TopLevel::TLShow(erase(self.arena, val)),
                        Err(_) => top,
                    }
                }
                TopLevel::TLDef(name, term) => TopLevel::TLDef(name, erase(self.arena, term)),
                other => other,
            })
            // Drop zero-param definitions whose body is a bare builtin
            // (type aliases like `def nat := int where ...`).
            .filter(|top| match top {
                TopLevel::TLDef(_, Term::Func(_, [], _, body))
                    if matches!(body, Term::Builtin(_)) =>
                {
                    false
                }
                _ => true,
            })
            .collect();
        self.tops.extend(evald_tops);
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

    /// Get the collected top-level items (for code generation).
    pub fn tops(&self) -> &[TopLevel<'bump>] {
        &self.tops
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
                Term::Func(_, [], _, Term::Refine(_, parent, predicate)) => {
                    println!("[refinement] {}", name);
                    self.checker.add_refinement(name, parent, predicate);
                }
                Term::Func(_, [], _, _) => {
                    println!("[defined] {}", name);
                    self.env.push((name, term));
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
