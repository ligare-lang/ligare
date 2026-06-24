//! De Bruijn index operations: substitution, shifting, and desugaring.
//!
//! This module centralises all de Bruijn index logic for the compiler:
//!
//! - **SubstitutionContext** — `subst`, `shift`, `beta`, `instantiate_pi`,
//!   and variant-aware traversals.  Used by evaluators (`eval`, `whnf`)
//!   and the type checker.
//! - **Desugarer** — resolves parser-produced `Named`/`NamedLam` nodes
//!   into de Bruijn `Var`/`Lam` form.

use crate::core::pool::TermArena;
use crate::core::syntax::{Tactic, Term};

// ───────────────────────────────────────────────
//  Desugarer: Named → Var, NamedLam → Lam
// ───────────────────────────────────────────────

/// Resolves `Named` variable references to de Bruijn `Var` indices
/// and converts `NamedLam` to `Lam`.
///
/// The parser generates terms using `Named` for all variable references and
/// `NamedLam(name, body)` for lambdas.  This pass walks the AST, tracks the
/// binding context (name stack), and replaces each `Named(name)` with `Var(i)`
/// where `i` is the position of `name` in the current name stack.
pub struct Desugarer<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> Desugarer<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Desugar a term: resolve all `NamedLam` → `Lam` and `Named` → `Var`.
    pub fn desugar(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.desugar_with_env(t, &[])
    }

    /// Recursive helper that carries a name stack `env` (innermost first).
    fn desugar_with_env(&self, t: &'bump Term<'bump>, env: &[&'bump str]) -> &'bump Term<'bump> {
        match t {
            // ── Named → Var resolution ──
            Term::Named(name) => {
                if let Some(i) = env.iter().position(|n| *n == *name) {
                    self.arena.var(i)
                } else {
                    t // free variable — stays as Named
                }
            }

            // ── NamedLam → Lam conversion ──
            Term::NamedLam(name, body) => {
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                self.arena.lam(self.desugar_with_env(body, &ext))
            }

            // ── Recurse into children ──
            Term::App(f, a) => self
                .arena
                .app(self.desugar_with_env(f, env), self.desugar_with_env(a, env)),
            Term::Lam(_) => {
                // Already-desugared Lam (from `def`): recurse into body with
                // a dummy binder since we don't know the name.
                // The body uses Var which already encodes binding, so just
                // recurse (Var indices are shifted appropriately by the Lam).
                t
            }
            Term::Pi(name, a, b) => {
                let a2 = self.desugar_with_env(a, env);
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                let b2 = self.desugar_with_env(b, &ext);
                self.arena.pi(name, a2, b2)
            }
            Term::Let(name, val, body, mc) => {
                let v2 = self.desugar_with_env(val, env);
                let mc2 = mc.map(|c| self.desugar_with_env(c, env));
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                let b2 = self.desugar_with_env(body, &ext);
                self.arena.let_(name, v2, b2, mc2)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                let c2 = self.desugar_with_env(cond, env);
                let t2 = self.desugar_with_env(tbranch, env);
                let f2 = self.desugar_with_env(fbranch, env);
                self.arena.if_then_else(c2, t2, f2)
            }
            Term::Annot(inner, c) => self.arena.annot(
                self.desugar_with_env(inner, env),
                self.desugar_with_env(c, env),
            ),
            Term::ByProof(inner, tactics) => {
                // Tactics contain terms that may have Named refs
                let inner2 = inner.map(|i| self.desugar_with_env(i, env));
                let tactics2: Vec<_> = tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => Tactic::Exact(self.desugar_with_env(t, env)),
                        Tactic::Apply(t) => Tactic::Apply(self.desugar_with_env(t, env)),
                        Tactic::Intro(n) => Tactic::Intro(*n),
                        Tactic::Have(n, t) => Tactic::Have(n, self.desugar_with_env(t, env)),
                    })
                    .collect();
                self.arena
                    .by_proof(inner2, self.arena.alloc_slice(&tactics2))
            }
            Term::Refine(name, parent, p) => {
                let p2 = self.desugar_with_env(parent, env);
                // Replace the refinement parameter reference with RefParam
                // BEFORE desugaring, so that prove_auto / subst_ref_param
                // can substitute the subject.  We must do this before
                // desugar_with_env because the latter could resolve
                // Named(name) to Var(i) if name shadows an outer binding.
                let pred_with_param = self.arena.map(p, &|node| {
                    if let Term::Named(n) = node
                        && *n == *name {
                            return Some(self.arena.ref_param());
                        }
                    None
                });
                let pred2 = self.desugar_with_env(pred_with_param, env);
                self.arena.refine(name, p2, pred2)
            }
            Term::Match(scrut, branches) => {
                let s2 = self.desugar_with_env(scrut, env);
                let bs2: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let mut ext: Vec<&'bump str> = binds.iter().map(|(n, _)| *n).collect();
                        ext.extend_from_slice(env);
                        let b2 = self.desugar_with_env(body, &ext);
                        let binds2: Vec<_> = binds
                            .iter()
                            .map(|(n, c)| (*n, self.desugar_with_env(c, env)))
                            .collect();
                        (*idx, self.arena.alloc_slice(&binds2), b2)
                    })
                    .collect();
                self.arena.match_(s2, self.arena.alloc_slice(&bs2))
            }
            Term::Variant(name, idx, payloads) => {
                let ps: Vec<_> = payloads
                    .iter()
                    .map(|p| self.desugar_with_env(p, env))
                    .collect();
                self.arena.variant(name, *idx, self.arena.alloc_slice(&ps))
            }
            Term::StructCons(name, fields) => {
                let fs: Vec<_> = fields
                    .iter()
                    .map(|f| self.desugar_with_env(f, env))
                    .collect();
                self.arena.struct_cons(name, self.arena.alloc_slice(&fs))
            }
            Term::StructProj(subject, idx) => self
                .arena
                .struct_proj(self.desugar_with_env(subject, env), *idx),

            // ── Leaf / no-name-binding nodes ──
            Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::Builtin(_)
            | Term::AutoProof
            | Term::RefParam
            | Term::UnionDef(..)
            | Term::StructDef(..) => t,
        }
    }
}

/// Convenience wrapper: desugar a term using a fresh `Desugarer`.
pub fn desugar<'bump>(arena: &'bump TermArena<'bump>, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
    Desugarer::new(arena).desugar(t)
}

// ───────────────────────────────────────────────
//  SubstitutionContext: subst / shift / beta
// ───────────────────────────────────────────────

/// Encapsulates de Bruijn index substitution and shifting operations.
///
/// These operations traverse the term tree and allocate new nodes in the
/// arena as needed.  By bundling the arena reference, callers avoid
/// passing it as a separate argument to every function.
pub struct SubstitutionContext<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> SubstitutionContext<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Substitute: replace de Bruijn index `i` with `s` in term `t`.
    pub fn subst(
        &self,
        s: &'bump Term<'bump>,
        i: usize,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.subst_cutoff(s, i, 0, t)
    }

    fn subst_cutoff(
        &self,
        s: &'bump Term<'bump>,
        i: usize,
        cutoff: usize,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        if let Term::Var(j) = t
            && *j == i + cutoff
        {
            return self.shift(cutoff as i32, 0, s);
        }
        self.traverse_children(t, cutoff as i32, |t, c| {
            self.subst_cutoff(s, i, c as usize, t)
        })
    }

    /// Shift: add `d` to all de Bruijn indices >= `cutoff`.
    pub fn shift(&self, d: i32, cutoff: i32, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Term::Var(j) = t
            && (*j as i32) >= cutoff
        {
            return self.arena.var((*j as i32 + d) as usize);
        }
        self.traverse_children(t, cutoff, |t, c| self.shift(d, c, t))
    }

    /// Shared children-recursion for `shift` and `subst_cutoff`.
    /// For nodes that bind variables (Lam, Pi, Let), `cutoff` is bumped.
    fn traverse_children(
        &self,
        t: &'bump Term<'bump>,
        cutoff: i32,
        recurse: impl Fn(&'bump Term<'bump>, i32) -> &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::Lam(body) => self.arena.lam(recurse(body, cutoff + 1)),
            Term::NamedLam(n, body) => self.arena.named_lam(n, recurse(body, cutoff + 1)),
            Term::App(f, a) => self.arena.app(recurse(f, cutoff), recurse(a, cutoff)),
            Term::Pi(n, a, b) => self.arena.pi(n, recurse(a, cutoff), recurse(b, cutoff + 1)),
            Term::Let(n, v, b, mc) => {
                let mc2 = mc.map(|c| recurse(c, cutoff));
                self.arena
                    .let_(n, recurse(v, cutoff), recurse(b, cutoff + 1), mc2)
            }
            Term::IfThenElse(c, th, el) => self.arena.if_then_else(
                recurse(c, cutoff),
                recurse(th, cutoff),
                recurse(el, cutoff),
            ),
            Term::Annot(inner, ct) => self
                .arena
                .annot(recurse(inner, cutoff), recurse(ct, cutoff)),
            Term::ByProof(inner, tactics) => {
                let inner_mapped = inner.map(|t| recurse(t, cutoff));
                let mapped: Vec<Tactic<'bump>> = tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => Tactic::Exact(recurse(t, cutoff)),
                        Tactic::Apply(t) => Tactic::Apply(recurse(t, cutoff)),
                        Tactic::Intro(_) => *tac,
                        Tactic::Have(n, t) => Tactic::Have(n, recurse(t, cutoff)),
                    })
                    .collect();
                self.arena
                    .by_proof(inner_mapped, self.arena.alloc_slice(&mapped))
            }
            Term::Refine(n, par, p) => {
                self.arena
                    .refine(n, recurse(par, cutoff), recurse(p, cutoff))
            }
            Term::UnionDef(name, variants) => {
                let mapped: Vec<_> = variants
                    .iter()
                    .map(|(vname, fields)| {
                        let mf: Vec<_> = fields
                            .iter()
                            .map(|(fnm, fc)| (*fnm, recurse(fc, cutoff)))
                            .collect();
                        (*vname, self.arena.alloc_slice(&mf))
                    })
                    .collect();
                self.arena.union_def(name, self.arena.alloc_slice(&mapped))
            }
            Term::Variant(name, idx, payloads) => {
                let mapped: Vec<_> = payloads.iter().map(|p| recurse(p, cutoff)).collect();
                self.arena
                    .variant(name, *idx, self.arena.alloc_slice(&mapped))
            }
            Term::Match(scrut, branches) => {
                let s = recurse(scrut, cutoff);
                let mapped: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let mb: Vec<_> = binds
                            .iter()
                            .map(|(n, c)| (*n, recurse(c, cutoff)))
                            .collect();
                        // branch body binds payload variables → bump cutoff
                        (
                            *idx,
                            self.arena.alloc_slice(&mb),
                            recurse(body, cutoff + binds.len() as i32),
                        )
                    })
                    .collect();
                self.arena.match_(s, self.arena.alloc_slice(&mapped))
            }
            Term::StructDef(name, fields) => {
                let mf: Vec<_> = fields
                    .iter()
                    .map(|(fnm, fc)| (*fnm, recurse(fc, cutoff)))
                    .collect();
                self.arena.struct_def(name, self.arena.alloc_slice(&mf))
            }
            Term::StructCons(name, field_values) => {
                let mapped: Vec<_> = field_values.iter().map(|v| recurse(v, cutoff)).collect();
                self.arena
                    .struct_cons(name, self.arena.alloc_slice(&mapped))
            }
            Term::StructProj(subject, idx) => {
                self.arena.struct_proj(recurse(subject, cutoff), *idx)
            }
            // Leaf nodes — returned unchanged (Var handled by callers)
            _ => t,
        }
    }

    /// Beta-reduction: substitute arg into the body of a lambda.
    pub fn beta(
        &self,
        lam_body: &'bump Term<'bump>,
        arg: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let shifted_arg = self.shift(1, 0, arg);
        let substituted = self.subst(shifted_arg, 0, lam_body);
        self.shift(-1, 0, substituted)
    }

    /// Peel the outermost Pi binder: substitute `arg` for Var(0) in the
    /// codomain, then shift the result by -1 to remove the binder.
    /// This is used when type-checking function application (both in
    /// `check_app` and `infer_fun_type`).
    pub fn instantiate_pi(
        &self,
        arg: &'bump Term<'bump>,
        codomain: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let substituted = self.subst(arg, 0, codomain);
        self.shift(-1, 0, substituted)
    }

    /// Shift that preserves `RefParam` (leaves it untouched).
    pub fn shift_preserve_refparam(&self, d: i32, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.shift_refparam_cutoff(d, 0, t)
    }

    fn shift_refparam_cutoff(
        &self,
        d: i32,
        cutoff: i32,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::RefParam => t,
            Term::Var(i) => {
                if (*i as i32) >= cutoff {
                    self.arena.var((*i as i32 + d) as usize)
                } else {
                    t
                }
            }
            _ => self.shift(d, cutoff, t),
        }
    }
}

// ───────────────────────────────────────────────
//  Destructuring helpers
// ───────────────────────────────────────────────

/// Build the projection terms for let-destructuring, shifting `val`'s
/// free de Bruijn indices to account for each layer of let-binding.
///
/// For `let Struct{f₁, f₂, ..., fₙ} := val in body`, the parser calls
/// this with `proj_names = ["Struct.f₁", "Struct.f₂", ...]` to obtain
/// `[Struct.f₁(val), Struct.f₂(shift¹(val)), ...]`.
///
/// The shift is applied via `SubstitutionContext::shift`, which correctly
/// bumps the cutoff at inner binders — unlike a naive `arena.map` over
/// `Var` nodes.
pub fn build_destruct_projections<'bump>(
    arena: &TermArena<'bump>,
    proj_names: &[&'bump str],
    val: &'bump Term<'bump>,
) -> Vec<&'bump Term<'bump>> {
    proj_names
        .iter()
        .enumerate()
        .map(|(i, name)| {
            let shifted_val = if i == 0 {
                val
            } else {
                shift_term(arena, i as i32, 0, val)
            };
            arena.app(arena.named(name), shifted_val)
        })
        .collect()
}

/// Shift de Bruijn indices — same semantics as `SubstitutionContext::shift`
/// but takes the arena with an unconstrained reference lifetime so it can
/// be called from contexts like the parser where the arena borrow doesn't
/// have lifetime `'bump`.
fn shift_term<'bump>(
    arena: &TermArena<'bump>,
    d: i32,
    cutoff: i32,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    if let Term::Var(j) = t
        && (*j as i32) >= cutoff
    {
        return arena.var((*j as i32 + d) as usize);
    }
    match t {
        Term::Lam(body) => arena.lam(shift_term(arena, d, cutoff + 1, body)),
        Term::NamedLam(n, body) => arena.named_lam(n, shift_term(arena, d, cutoff + 1, body)),
        Term::App(f, a) => arena.app(
            shift_term(arena, d, cutoff, f),
            shift_term(arena, d, cutoff, a),
        ),
        Term::Pi(n, a, b) => arena.pi(
            n,
            shift_term(arena, d, cutoff, a),
            shift_term(arena, d, cutoff + 1, b),
        ),
        Term::Let(n, v, b, mc) => {
            let mc2 = mc.map(|c| shift_term(arena, d, cutoff, c));
            arena.let_(
                n,
                shift_term(arena, d, cutoff, v),
                shift_term(arena, d, cutoff + 1, b),
                mc2,
            )
        }
        Term::IfThenElse(c, th, el) => arena.if_then_else(
            shift_term(arena, d, cutoff, c),
            shift_term(arena, d, cutoff, th),
            shift_term(arena, d, cutoff, el),
        ),
        Term::Annot(inner, ct) => arena.annot(
            shift_term(arena, d, cutoff, inner),
            shift_term(arena, d, cutoff, ct),
        ),
        // All other nodes: return unchanged (no Var children that need shifting
        // beyond what's already covered by recursive cases, or leaf nodes).
        _ => t,
    }
}
