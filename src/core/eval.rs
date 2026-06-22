//! Strong evaluator — reduces terms to (full) normal form.
//!
//! Unlike `whnf`, this evaluator fully computes recursive function calls
//! (via `inject_self`) and evaluates arguments eagerly for primitive
//! operations.  It is used at the top level (`--eval`, `#show`) where
//! the user explicitly requests runtime computation.
//!
//! During type checking, prefer `WhnfEvaluator` from `crate::core::whnf`.

use crate::core::pool::{SubstitutionContext, TermArena};
use crate::core::syntax::{Name, Tactic, Term};
use crate::pretty::pretty;

/// Strong evaluator — reduces terms to normal form using a bump arena
/// for intermediate allocations.
///
/// Encapsulates the arena and substitution context, providing a clean
/// interface where evaluation state is bundled with its operations.
pub struct Evaluator<'bump> {
    arena: &'bump TermArena<'bump>,
    sub: SubstitutionContext<'bump>,
    /// If set, `Builtin(self_name)` in function bodies is replaced
    /// with the self-term during beta-reduction (enables recursion).
    self_name: Option<Name<'bump>>,
}

impl<'bump> Evaluator<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self {
            arena,
            sub: SubstitutionContext::new(arena),
            self_name: None,
        }
    }

    /// Set the name used for self-reference injection during beta-reduction.
    pub fn set_self_name(&mut self, name: Name<'bump>) {
        self.self_name = Some(name);
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
            Term::ByProof(inner, tactics) => {
                if let Some(inner) = inner {
                    self.eval(inner)
                } else {
                    // Standalone proof: mechanically expand tactics.
                    // Only `intro` + `exact` is supported here;
                    // `apply` requires type information not available in eval.
                    let expanded = self.expand_proof_tactics(tactics)?;
                    self.eval(expanded)
                }
            }
            Term::Refine(name, parent, p) => {
                let parent_val = self.eval(parent)?;
                let p_val = self.eval(p)?;
                Ok(self.arena.refine(name, parent_val, p_val))
            }
            Term::AutoProof => Ok(t),
            Term::RefParam => Ok(t),
            // Leaf values
            Term::Pi(_, _, _)
            | Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::Builtin(_) => Ok(t),
            Term::UnionDef(..) => Ok(t),
            Term::Variant(name, idx, payloads) => {
                let ep: Vec<_> = payloads
                    .iter()
                    .map(|p| self.eval(p))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.variant(name, *idx, self.arena.alloc_slice(&ep)))
            }
            Term::Match(scrut, branches) => {
                let s = self.eval(scrut)?;
                if let Term::Variant(_, idx, payloads) = s {
                    if let Some((_, _, body)) = branches.get(*idx) {
                        let mut result = *body;
                        for payload in payloads.iter().rev() {
                            result = self.sub.beta(result, payload);
                        }
                        return self.eval(result);
                    }
                }
                // Stuck — keep the match expression
                let bs: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let bb = self.eval(body).unwrap_or(body);
                        (*idx, *binds, bb)
                    })
                    .collect();
                Ok(self.arena.match_(s, self.arena.alloc_slice(&bs)))
            }
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
                let body2 = self.inject_self(f, body);
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

    /// Replace `Builtin(self_name)` references with the self-term in a body.
    ///
    /// If `self_name` is `Some(name)`, every `Builtin(name)` in `t` is
    /// replaced by `self_term` (the enclosing `Lam`).  This enables
    /// recursion without a dedicated `This` AST node.
    fn inject_self(
        &self,
        self_term: &'bump Term<'bump>,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        if let Some(name) = self.self_name {
            self.arena.map(t, &|node| {
                if let Term::Builtin(n) = node
                    && *n == name
                {
                    Some(self_term)
                } else {
                    None
                }
            })
        } else {
            t
        }
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
                    return Err("Expected PrimOp".to_string());
                };
                Ok(self.arena.alloc(op.apply(*x, *y)))
            }
            _ => Err(format!(
                "Arithmetic on non-integer: {} and {}",
                pretty(x),
                pretty(y)
            )),
        }
    }

    /// Mechanically expand `intro*; exact t` tactics to a lambda term.
    /// This is used for standalone `by` blocks at runtime.
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
                Tactic::Exact(_) => {
                    return Err("`exact` must be the last tactic".into());
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
pub fn eval<'bump>(
    arena: &'bump TermArena<'bump>,
    t: &'bump Term<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    Evaluator::new(arena).eval(t)
}

/// Evaluate with self-reference injection (for recursive functions).
pub fn eval_with_self<'bump>(
    arena: &'bump TermArena<'bump>,
    t: &'bump Term<'bump>,
    self_name: Name<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    let mut ev = Evaluator::new(arena);
    ev.set_self_name(self_name);
    ev.eval(t)
}
