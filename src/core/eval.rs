//! Strong evaluator — reduces terms to (full) normal form.
//!
//! Unlike `whnf`, this evaluator fully computes recursive function calls
//! (via `replace_this`) and evaluates arguments eagerly for primitive
//! operations.  It is used at the top level (`--eval`, `#show`) where
//! the user explicitly requests runtime computation.
//!
//! During type checking, prefer `WhnfEvaluator` from `crate::core::whnf`.

use crate::core::pool::{SubstitutionContext, TermArena};
use crate::core::syntax::Term;
use crate::pretty::pretty;

/// Strong evaluator — reduces terms to normal form using a bump arena
/// for intermediate allocations.
///
/// Encapsulates the arena and substitution context, providing a clean
/// interface where evaluation state is bundled with its operations.
pub struct Evaluator<'bump> {
    arena: &'bump TermArena<'bump>,
    sub: SubstitutionContext<'bump>,
}

impl<'bump> Evaluator<'bump> {
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

    /// Evaluate a term to normal form (strong evaluation).
    ///
    /// May allocate intermediate terms in the arena; the result lives in the arena.
    pub fn eval(&self, t: &'bump Term<'bump>) -> Result<&'bump Term<'bump>, String> {
        match t {
            Term::App(f, a) => self.eval_app(f, a),
            Term::Lam(_) => Ok(t),
            Term::Let(_name, val, body, _mconstr) => {
                let b = self.sub.beta(body, val);
                self.eval(b)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => self.eval_if(cond, tbranch, fbranch),
            Term::Annot(inner, _) => self.eval(inner),
            Term::ByProof(inner, _) => self.eval(inner),
            Term::Refine(name, parent, p) => {
                let parent_val = self.eval(parent)?;
                let p_val = self.eval(p)?;
                Ok(self.arena.refine(name, parent_val, p_val))
            }
            Term::AutoProof => Ok(t),
            Term::RefParam => Ok(t),
            Term::This => Ok(t),
            Term::Func { .. } => {
                let d = crate::core::desugar::Desugarer::new(self.arena).desugar(t);
                self.eval(d)
            }
            Term::ProofBlock(inner) => self.eval(inner),
            // Leaf values
            Term::Pi(_, _, _)
            | Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::Builtin(_) => Ok(t),
        }
    }

    // ── private evaluation helpers ──

    fn eval_app(
        &self,
        f: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        match f {
            Term::Lam(body) => {
                let body2 = self.replace_this(f, body);
                let b = self.sub.beta(body2, a);
                self.eval(b)
            }
            Term::App(prim, first) if matches!(prim, Term::PrimOp(_)) => {
                let a_val = self.eval(a)?;
                let first_val = self.eval(first)?;
                self.eval_arith(prim, first_val, a_val)
            }
            _ => {
                let f_val = self.eval(f)?;
                if matches!(f_val, Term::Lam(_)) {
                    self.eval(self.arena.app(f_val, a))
                } else {
                    Ok(self.arena.app(f_val, a))
                }
            }
        }
    }

    /// Replace all `This` references with the self-reference (the Lam itself).
    fn replace_this(
        &self,
        self_term: &'bump Term<'bump>,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if matches!(node, Term::This) {
                Some(self_term)
            } else {
                None
            }
        })
    }

    fn eval_if(
        &self,
        cond: &'bump Term<'bump>,
        tbranch: &'bump Term<'bump>,
        fbranch: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        let cond_val = self.eval(cond)?;
        match cond_val {
            Term::LitBool(true) => self.eval(tbranch),
            Term::LitBool(false) => self.eval(fbranch),
            _ => Ok(self.arena.if_then_else(cond_val, tbranch, fbranch)),
        }
    }

    fn eval_arith(
        &self,
        prim: &Term<'_>,
        x: &Term<'_>,
        y: &Term<'_>,
    ) -> Result<&'bump Term<'bump>, String> {
        match (x, y) {
            (Term::LitInt(x), Term::LitInt(y)) => {
                let Term::PrimOp(op) = prim else {
                    return Err("expected PrimOp".to_string());
                };
                Ok(self.arena.alloc(op.apply(*x, *y)))
            }
            _ => Err(format!(
                "arithmetic on non-integer: {} and {}.",
                pretty(x),
                pretty(y)
            )),
        }
    }
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn eval<'bump>(
    arena: &'bump TermArena<'bump>,
    t: &'bump Term<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    Evaluator::new(arena).eval(t)
}
