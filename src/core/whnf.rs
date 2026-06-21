//! Weak Head Normal Form (WHNF) evaluator.
//!
//! WHNF stops at constructors and does not evaluate under binders or
//! force evaluation of non-strict arguments.  This is the evaluator used
//! by the type checker — it normalizes types and constraints without
//! computing runtime values (e.g. recursive function calls).
//!
//! Key differences from the strong evaluator (`eval`):
//! - `This` is left untouched — recursive calls are NOT unrolled.
//! - PrimOp applications only reduce when both operands are already
//!   `LitInt` (no eager argument evaluation).
//! - Argument terms in `App(f, a)` are never forced when `f` is not a
//!   `Lam` or `PrimOp` application.

use crate::core::pool::{SubstitutionContext, TermArena};
use crate::core::syntax::{Tactic, Term};

/// Weak Head Normal Form evaluator.
///
/// Encapsulates the arena and substitution context, providing a clean
/// interface for type-checking purposes where full normalisation is
/// neither needed nor desirable.
pub struct WhnfEvaluator<'bump> {
    arena: &'bump TermArena<'bump>,
    sub: SubstitutionContext<'bump>,
}

impl<'bump> WhnfEvaluator<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self {
            arena,
            sub: SubstitutionContext::new(arena),
        }
    }

    /// Access the underlying arena.
    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Access the substitution context.
    pub fn substitution(&self) -> &SubstitutionContext<'bump> {
        &self.sub
    }

    /// Evaluate a term to Weak Head Normal Form.
    pub fn whnf(&self, t: &'bump Term<'bump>) -> Result<&'bump Term<'bump>, String> {
        match t {
            Term::App(f, a) => self.whnf_app(f, a),
            Term::Lam(_) => Ok(t),
            Term::Let(_name, val, body, _mconstr) => self.whnf(self.sub.beta(body, val)),
            Term::IfThenElse(cond, tbranch, fbranch) => self.whnf_if(cond, tbranch, fbranch),
            Term::Annot(inner, _) => self.whnf(inner),
            Term::ByProof(inner, tactics) => {
                if let Some(inner) = inner {
                    self.whnf(inner)
                } else {
                    let expanded = self.expand_proof_tactics(tactics)?;
                    self.whnf(expanded)
                }
            }
            Term::Refine(name, parent, p) => {
                let parent_val = self.whnf(parent)?;
                let p_val = self.whnf(p)?;
                Ok(self.arena.refine(name, parent_val, p_val))
            }
            Term::Func { .. } => {
                let d = crate::core::desugar::Desugarer::new(self.arena).desugar(t);
                self.whnf(d)
            }
            // Leaf values — already in WHNF
            _ => Ok(t),
        }
    }

    // ── private helpers ──

    fn whnf_app(
        &self,
        f: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        match f {
            Term::Lam(body) => self.whnf(self.sub.beta(body, a)),
            Term::App(prim, first) if matches!(prim, Term::PrimOp(_)) => {
                let a_val = self.whnf(a)?;
                let first_val = self.whnf(first)?;
                match (first_val, a_val) {
                    (Term::LitInt(x), Term::LitInt(y)) => {
                        let Term::PrimOp(op) = *prim else {
                            unreachable!()
                        };
                        Ok(self.arena.alloc(op.apply(*x, *y)))
                    }
                    _ => {
                        let prim2 = self.arena.prim_op(if let Term::PrimOp(op) = *prim {
                            *op
                        } else {
                            unreachable!()
                        });
                        Ok(self.arena.app(self.arena.app(prim2, first_val), a_val))
                    }
                }
            }
            _ => {
                let f_val = self.whnf(f)?;
                if matches!(f_val, Term::Lam(_)) {
                    self.whnf(self.arena.app(f_val, a))
                } else {
                    Ok(self.arena.app(f_val, a))
                }
            }
        }
    }

    fn whnf_if(
        &self,
        cond: &'bump Term<'bump>,
        tbranch: &'bump Term<'bump>,
        fbranch: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        let cond_val = self.whnf(cond)?;
        match cond_val {
            Term::LitBool(true) => self.whnf(tbranch),
            Term::LitBool(false) => self.whnf(fbranch),
            _ => Ok(self.arena.if_then_else(cond_val, tbranch, fbranch)),
        }
    }

    /// Mechanically expand `intro*; exact t` tactics to a lambda term.
    fn expand_proof_tactics(
        &self,
        tactics: &'bump [Tactic<'bump>],
    ) -> Result<&'bump Term<'bump>, String> {
        let mut intro_count = 0usize;
        let n = tactics.len();
        for (i, tactic) in tactics.iter().enumerate() {
            let is_last = i == n - 1;
            match tactic {
                Tactic::Intro(_) if !is_last => intro_count += 1,
                Tactic::Exact(t) if is_last => {
                    let mut result = *t;
                    for _ in 0..intro_count {
                        result = self.arena.lam(result);
                    }
                    return Ok(result);
                }
                _ => {
                    return Err(
                        "Only `intro`+`exact` tactics are supported in standalone proof eval"
                            .into(),
                    );
                }
            }
        }
        Err("Proof block must end with `exact`".into())
    }
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn whnf<'bump>(
    arena: &'bump TermArena<'bump>,
    t: &'bump Term<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    WhnfEvaluator::new(arena).whnf(t)
}
