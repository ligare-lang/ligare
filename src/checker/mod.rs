pub mod builtin;
pub mod context;
pub mod infer;
pub mod prove;

use crate::checker::context::{ConstraintTable, Context, add_refine, empty_table};
use crate::core::desugar::Desugarer;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Term};
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
            Term::ByProof(t, _proof) => self.check(ctx, t, constraint),
            Term::Refine(name, parent, p) => {
                let new_table = add_refine(name, parent, p, &self.table);
                let checker = Self::with_table(self.arena, &new_table);
                checker.check(ctx, constraint, constraint)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                self.check_if(ctx, cond, tbranch, fbranch, constraint)
            }
            Term::ProofBlock(proof_term) => {
                let evald = self.evaluator.whnf(term)?;
                self.prove_with(ctx, evald, constraint, proof_term)
            }
            Term::Let(_name, val, body, mconstr) => {
                self.check_let(ctx, val, body, *mconstr, constraint)
            }
            // Application: use the function's type rather than forcing
            // full evaluation (which would compute recursive calls).
            Term::App(f, a) => self.check_app(ctx, f, a, constraint),
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
