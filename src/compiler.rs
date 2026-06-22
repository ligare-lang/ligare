use std::fs;

use bumpalo::Bump;

use crate::backend::ir::FunSig;
use crate::checker::TypeChecker;
use crate::checker::context::empty_ctx;
use crate::checker::erase::Eraser;
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
    /// Function signatures extracted before erasure (for C codegen).
    fun_sigs: Vec<(&'bump str, FunSig)>,
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
            fun_sigs: vec![],
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
        // Extract function signatures from the original (un-erased) terms
        // so the C backend can emit correct parameter and return types.
        for top in &tops {
            match top {
                TopLevel::TLDef(name, term) => {
                    if let Term::Func(_, params, m_ret, _) = term {
                        self.fun_sigs
                            .push((name, FunSig::from_func(params, *m_ret)));
                    }
                }
                TopLevel::TLTheorem(name, _, body) => {
                    if let Term::Func(_, params, m_ret, _) = body {
                        self.fun_sigs
                            .push((name, FunSig::from_func(params, *m_ret)));
                    }
                }
                _ => {}
            }
        }
        let eraser = Eraser::new(self.arena);
        let evald_tops: Vec<TopLevel<'bump>> = tops
            .into_iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(name, term) => {
                    let resolved = self.subst_top_level(term);
                    Some(TopLevel::TLDef(name, eraser.erase(resolved)))
                }
                TopLevel::TLShow(term) | TopLevel::TLExpr(term) => {
                    let resolved = self.subst_top_level(term);
                    match self.evaluator.eval(resolved) {
                        Ok(val) => Some(TopLevel::TLShow(eraser.erase(val))),
                        Err(_) => Some(TopLevel::TLShow(eraser.erase(resolved))),
                    }
                }
                TopLevel::TLTheorem(name, _, body) => {
                    let resolved_body = self.subst_top_level(body);
                    Some(TopLevel::TLDef(name, eraser.erase(resolved_body)))
                }
                TopLevel::TLCheck(_, _) => None,
            })
            // Drop zero-param definitions whose body is a bare builtin
            // (type aliases like `def nat := int where ...`).
            .filter(|top| match top {
                TopLevel::TLDef(_, Term::Func(_, params, _, body))
                    if params.is_empty() && matches!(body, Term::Builtin(_)) =>
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

    /// Get the function signatures extracted before erasure (for C codegen).
    pub fn fun_sigs(&self) -> &[(&'bump str, FunSig)] {
        &self.fun_sigs
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
            TopLevel::TLTheorem(name, prop, body) => {
                let resolved_body = self.subst_top_level(body);
                let resolved_prop = self.subst_top_level(prop);
                match self
                    .checker
                    .check(&empty_ctx(), resolved_body, resolved_prop)
                {
                    Err(err) => return Err(format!("theorem check failed: {}", err)),
                    Ok(_) => {
                        println!("[theorem] {}", name);
                        self.env.push((name, body));
                    }
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
