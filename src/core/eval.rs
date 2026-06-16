use crate::core::pool::{SubstitutionContext, TermArena};
use crate::core::syntax::{PrimOp, Term};
use crate::pretty::pretty;

/// Evaluates terms to normal form using a bump arena for intermediate allocations.
///
/// Encapsulates the arena and substitution context, providing a clean
/// OOP interface where evaluation state is bundled with its operations.
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

    /// Evaluate a term to normal form.
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
            Term::App(prim, first) if self.is_prim_op(prim) => {
                let a_val = self.eval(a)?;
                let first_val = self.eval(first)?;
                self.eval_arith(prim, first_val, a_val)
            }
            _ => {
                let f_val = self.eval(f)?;
                if matches!(f_val, Term::Lam(_)) {
                    let app = self.arena.app(f_val, a);
                    self.eval(app)
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
        match t {
            Term::This => self_term,
            Term::App(f, a) => {
                let f2 = self.replace_this(self_term, f);
                let a2 = self.replace_this(self_term, a);
                self.arena.app(f2, a2)
            }
            Term::Lam(b) => {
                let b2 = self.replace_this(self_term, b);
                self.arena.lam(b2)
            }
            Term::Let(n, v, b, mc) => {
                let v2 = self.replace_this(self_term, v);
                let b2 = self.replace_this(self_term, b);
                let mc2 = mc.map(|c| self.replace_this(self_term, c));
                self.arena.let_(n, v2, b2, mc2)
            }
            Term::IfThenElse(c, th, el) => {
                let c2 = self.replace_this(self_term, c);
                let th2 = self.replace_this(self_term, th);
                let el2 = self.replace_this(self_term, el);
                self.arena.if_then_else(c2, th2, el2)
            }
            Term::Annot(inner, c) => {
                let inner2 = self.replace_this(self_term, inner);
                let c2 = self.replace_this(self_term, c);
                self.arena.annot(inner2, c2)
            }
            Term::ByProof(inner, p) => {
                let inner2 = self.replace_this(self_term, inner);
                let p2 = self.replace_this(self_term, p);
                self.arena.by_proof(inner2, p2)
            }
            Term::Refine(n, par, p) => {
                let par2 = self.replace_this(self_term, par);
                let p2 = self.replace_this(self_term, p);
                self.arena.refine(n, par2, p2)
            }
            Term::Pi(n, a, b) => {
                let a2 = self.replace_this(self_term, a);
                let b2 = self.replace_this(self_term, b);
                self.arena.pi(n, a2, b2)
            }
            Term::ProofBlock(inner) => {
                let inner2 = self.replace_this(self_term, inner);
                self.arena.proof_block(inner2)
            }
            // Leaf nodes — return as-is
            _ => t,
        }
    }

    fn is_prim_op(&self, t: &Term<'_>) -> bool {
        matches!(t, Term::PrimOp(_))
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
                Ok(self.arena.alloc(Self::arith_result(*op, *x, *y)))
            }
            _ => Err(format!("arithmetic on non-integer: {} and {}.", pretty(x), pretty(y))),
        }
    }

    /// Compute the integer/bool result of a primitive operation.
    fn arith_result(op: PrimOp, x: i64, y: i64) -> Term<'static> {
        match op {
            PrimOp::Add => Term::LitInt(x.wrapping_add(y)),
            PrimOp::Sub => Term::LitInt(x.wrapping_sub(y)),
            PrimOp::Mul => Term::LitInt(x.wrapping_mul(y)),
            PrimOp::Div => {
                if y == 0 {
                    Term::LitInt(0)
                } else {
                    Term::LitInt(x / y)
                }
            }
            PrimOp::Mod_ => {
                if y == 0 {
                    Term::LitInt(0)
                } else {
                    Term::LitInt(x % y)
                }
            }
            PrimOp::Eq => Term::LitBool(x == y),
            PrimOp::Lt => Term::LitBool(x < y),
            PrimOp::Gt => Term::LitBool(x > y),
            PrimOp::Le => Term::LitBool(x <= y),
            PrimOp::Ge => Term::LitBool(x >= y),
            PrimOp::Neq => Term::LitBool(x != y),
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
