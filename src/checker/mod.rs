pub mod builtin;
pub mod context;
pub mod erase;
pub mod infer;
pub mod prove;

use crate::checker::builtin::check_builtin;
use crate::checker::context::{ConstraintTable, Context, add_refine, empty_table, lookup_refine};
use crate::core::desugar::Desugarer;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Tactic, Term};
use crate::core::whnf::WhnfEvaluator;

/// The type checker — bundles arena, constraint table, and checking logic.
///
/// Maintains a constraint table that is mutated when refinement definitions
/// are encountered (via `add_refinement`).  Individual `check` calls may
/// create temporary table clones without mutating the persistent state.
pub struct TypeChecker<'bump> {
    pub(crate) arena: &'bump TermArena<'bump>,
    pub(crate) evaluator: WhnfEvaluator<'bump>,
    pub(crate) desugarer: Desugarer<'bump>,
    table: ConstraintTable<'bump>,
}

impl<'bump> TypeChecker<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self {
            arena,
            evaluator: WhnfEvaluator::new(arena),
            desugarer: Desugarer::new(arena),
            table: empty_table(),
        }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Add a refinement definition to the persistent constraint table.
    pub fn add_refinement(
        &mut self,
        name: Name<'bump>,
        parent: &'bump Term<'bump>,
        predicate: &'bump Term<'bump>,
    ) {
        self.table.insert(0, (name, parent, predicate));
    }

    /// Get a reference to the persistent constraint table.
    pub fn table(&self) -> &ConstraintTable<'bump> {
        &self.table
    }

    /// Check a term against a constraint.
    pub fn check(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let desugared = self.desugarer.desugar(term);
        match desugared {
            Term::Var(i) => self.check_var(ctx, *i, constraint),
            Term::Annot(t, c) => {
                if let (Term::Pi(..), Term::Pi(..)) = (c, constraint) {
                    self.check_pi_match(c, constraint)?;
                }
                self.check(ctx, t, c)?;
                self.check(ctx, t, constraint)
            }
            Term::ByProof(t_opt, tactics) => {
                let c_nf = self.evaluator.whnf(constraint)?;
                // Expand Builtin constraints (like `nat`) that are
                // actually refinement constraints in the table.
                let expanded = match c_nf {
                    Term::Builtin(name) => lookup_refine(name, &self.table)
                        .map(|(p, pr)| self.arena.refine(name, p, pr)),
                    _ => None,
                };
                let effective = expanded.as_deref().unwrap_or(c_nf);
                match effective {
                    Term::Refine(_, parent, pred) => {
                        // Refinement: subject must satisfy parent, tactics prove predicate.
                        if let Some(subj) = t_opt {
                            self.check(ctx, subj, parent)?;
                            self.execute_tactics(ctx, Some(subj), pred, tactics)
                        } else {
                            // No subject — tactics build the whole proof.
                            let (proof, final_ctx) =
                                self.build_proof_from_tactics(ctx, None, constraint, tactics)?;
                            self.check(&final_ctx, proof, constraint)
                        }
                    }
                    _ => {
                        // Non-refinement: first try checking the subject
                        // directly (tactics are just evidence).  If that
                        // fails AND the tactics include intro/apply
                        // (which wrap the subject), fall back to building
                        // a proof from tactics.  Otherwise propagate the
                        // original error.
                        if let Some(subj) = t_opt {
                            if self.check(ctx, subj, constraint).is_ok() {
                                return Ok(());
                            }
                            let has_wrapping = tactics
                                .iter()
                                .any(|t| matches!(t, Tactic::Intro(_) | Tactic::Apply(_)));
                            if !has_wrapping {
                                return self.check(ctx, subj, constraint);
                            }
                        }
                        let (proof, final_ctx) =
                            self.build_proof_from_tactics(ctx, *t_opt, constraint, tactics)?;
                        self.check(&final_ctx, proof, constraint)
                    }
                }
            }
            Term::Refine(name, parent, p) => {
                let new_table = add_refine(name, parent, p, &self.table);
                let checker = Self::with_table(self.arena, &new_table);
                checker.check(ctx, constraint, constraint)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                self.check_if(ctx, cond, tbranch, fbranch, constraint)
            }
            Term::Let(_name, val, body, mconstr) => {
                self.check_let(ctx, val, body, *mconstr, constraint)
            }
            // Application: use the function's type rather than forcing
            // full evaluation (which would compute recursive calls).
            Term::App(f, a) => self.check_app(ctx, f, a, constraint),
            // A bare Builtin name may be a type (int, str, etc.) or a
            // refinement (nat).  If neither, it's an undefined variable.
            Term::Builtin(name) => {
                if check_builtin(name).is_some() || lookup_refine(name, &self.table).is_some() {
                    self.check_by_constraint(ctx, desugared, constraint)
                } else {
                    Err(format!("Undefined variable: {}", name))
                }
            }
            _ => self.check_by_constraint(ctx, desugared, constraint),
        }
    }

    /// Create a temporary checker with a different table (for sub-checks).
    pub(crate) fn with_table(
        arena: &'bump TermArena<'bump>,
        table: &ConstraintTable<'bump>,
    ) -> Self {
        Self {
            arena,
            evaluator: WhnfEvaluator::new(arena),
            desugarer: Desugarer::new(arena),
            table: table.clone(),
        }
    }
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn check<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    term: &'bump Term<'bump>,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    let checker = TypeChecker {
        arena,
        evaluator: WhnfEvaluator::new(arena),
        desugarer: Desugarer::new(arena),
        table: table.clone(),
    };
    checker.check(ctx, term, constraint)
}
