//! Weak Head Normal Form (WHNF) evaluator.
//!
//! WHNF stops at constructors and does not evaluate under binders or
//! force evaluation of non-strict arguments.  This is the evaluator used
//! by the constraint checker — it normalizes constraints without computing
//! runtime terms such as recursive calls.
//!
//! Key differences from the strong evaluator (`eval`):
//! - `This` is left untouched — recursive calls are NOT unrolled.
//! - PrimOp applications only reduce when both operands are already
//!   `LitInt` (no eager argument evaluation).
//! - Argument terms in `App(f, a)` are never forced when `f` is not a
//!   `Lam` or `PrimOp` application.

use crate::core::debruijn::SubstitutionContext;
use crate::core::pool::TermArena;
use crate::core::syntax::Term;

/// Weak Head Normal Form evaluator.
///
/// Encapsulates the arena and substitution context, providing a clean
/// interface for constraint-checking purposes where full normalisation is
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
            Term::Implicit(inner) => self.whnf(inner),
            Term::Lam(_) => Ok(t),
            Term::Let(_name, val, body, _mconstr) => self.whnf(self.sub.beta(body, val)),
            Term::IfThenElse(cond, tbranch, fbranch) => self.whnf_if(cond, tbranch, fbranch),
            Term::Annot(inner, _) => self.whnf(inner),
            Term::Unsafe(inner) => self.whnf(inner),
            Term::Pure(inner) => self.whnf(inner),
            Term::ByProof(inner, tactics) => {
                if let Some(inner) = inner {
                    self.whnf(inner)
                } else {
                    let expanded = self.arena.expand_proof_tactics(tactics)?;
                    self.whnf(expanded)
                }
            }
            Term::Refine(name, parent, p) => {
                let parent_val = self.whnf(parent)?;
                let p_val = self.whnf(p)?;
                Ok(self.arena.refine(name, parent_val, p_val))
            }
            // Leaf values — already in WHNF
            Term::Pi(_, _, _)
            | Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::Builtin(_)
            | Term::Global(_)
            | Term::AutoProof
            | Term::RefParam => Ok(t),
            Term::Named(_) => Err("Named identifier reached WHNF before desugaring".into()),
            Term::NamedLam(_, _) => Err("NamedLam reached WHNF before desugaring".into()),
            Term::Do(_) => Err("Do block reached WHNF before desugaring".into()),
            Term::EnumDef(..) => Ok(t),
            Term::StructDef(..) => Ok(t),
            Term::StructCons(name, field_values) => {
                let ev: Vec<_> = field_values
                    .iter()
                    .map(|v| self.whnf(v))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.struct_cons(name, self.arena.alloc_slice(&ev)))
            }
            Term::StructProj(subject, idx) => {
                let mut s = self.whnf(subject)?;
                while let Term::Annot(inner, _) = s {
                    s = self.whnf(inner)?;
                }
                if let Term::StructCons(_, field_values) = s {
                    field_values
                        .get(*idx)
                        .copied()
                        .ok_or_else(|| format!("Struct projection index {} out of bounds", idx))
                } else {
                    Ok(self.arena.struct_proj(s, *idx))
                }
            }
            Term::Variant(name, idx, payloads) => {
                let ep: Vec<_> = payloads
                    .iter()
                    .map(|p| self.whnf(p))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.variant(name, *idx, self.arena.alloc_slice(&ep)))
            }
            Term::Match(scrut, branches) => {
                let s = self.whnf(scrut)?;
                if let Term::Variant(_, idx, payloads) = s {
                    // Found a concrete variant — select the matching branch
                    if let Some((_, _binds, body)) = branches.get(*idx) {
                        // Bind payload values to branch body via beta reduction
                        let mut result = *body;
                        // Bind in reverse order (innermost first)
                        for payload in payloads.iter().rev() {
                            result = self.sub.beta(result, payload);
                        }
                        return self.whnf(result);
                    }
                }
                // Scrutinee is not a variant — stuck; normalize branches
                let bs: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let eb: Vec<_> = binds
                            .iter()
                            .map(|(n, c)| {
                                let cn = self.whnf(c).unwrap_or(c);
                                (*n, cn)
                            })
                            .collect();
                        let bb = self.whnf(body).unwrap_or(body);
                        (*idx, self.arena.alloc_slice(&eb), bb)
                    })
                    .collect();
                Ok(self.arena.match_(s, self.arena.alloc_slice(&bs)))
            }
            Term::NamedMatch(..) => Err("NamedMatch reached WHNF before desugaring".into()),
            Term::MethodCall(..) => Err("MethodCall reached WHNF before resolution".into()),
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
                // Normalize arrow type: App(App(->, A), B) → Pi("", A, B)
                if let Term::App(builtin, dom) = f
                    && matches!(*builtin, Term::Builtin(n) | Term::Global(n) if *n == "->")
                {
                    let dom_nf = self.whnf(dom)?;
                    let cod_nf = self.whnf(a)?;
                    return Ok(self.arena.pi(self.arena.alloc_str(""), dom_nf, cod_nf));
                }
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
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn whnf<'bump>(
    arena: &'bump TermArena<'bump>,
    t: &'bump Term<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    WhnfEvaluator::new(arena).whnf(t)
}
