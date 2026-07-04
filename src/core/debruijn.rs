//! De Bruijn index operations: substitution, shifting, and desugaring.
//!
//! This module centralises all de Bruijn index logic for the compiler:
//!
//! - **SubstitutionContext** — `subst`, `shift`, `beta`, `instantiate_pi`,
//!   and variant-aware traversals.  Used by evaluators (`eval`, `whnf`)
//!   and the constraint checker.
//! - **Desugarer** — resolves parser-produced `Named`/`NamedLam` nodes
//!   into de Bruijn `Var`/`Lam` form.

use crate::config::{BUILTIN_DATA, BUILTIN_IO};
use crate::core::pool::TermArena;
use crate::core::syntax::{DoStmt, Name, Tactic, Term};

pub type VariantLookup<'bump> = (
    &'bump str,
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
);

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
pub struct Desugarer<'arena, 'bump> {
    arena: &'arena TermArena<'bump>,
}

#[derive(Clone, Copy)]
struct EffectContext;

impl<'arena, 'bump> Desugarer<'arena, 'bump> {
    pub fn new(arena: &'arena TermArena<'bump>) -> Self {
        Self { arena }
    }

    pub fn arena(&self) -> &'arena TermArena<'bump> {
        self.arena
    }

    /// Desugar a term: resolve all `NamedLam` → `Lam` and `Named` → `Var`.
    pub fn desugar(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.try_desugar(t)
            .expect("desugar failed; use try_desugar for context-dependent parser nodes")
    }

    pub fn try_desugar(&self, t: &'bump Term<'bump>) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_without_variant_resolver(t, &[])
    }

    pub fn try_desugar_with_variant_resolver(
        &self,
        t: &'bump Term<'bump>,
        resolver: &impl Fn(&str) -> Option<VariantLookup<'bump>>,
    ) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_with_env(t, &[], Some(resolver), None)
    }

    /// Desugar a term with an existing innermost-first local environment.
    pub fn desugar_with_names(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
    ) -> &'bump Term<'bump> {
        self.try_desugar_with_names(t, env)
            .expect("desugar failed; use try_desugar_with_names for context-dependent parser nodes")
    }

    pub fn try_desugar_with_names(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
    ) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_without_variant_resolver(t, env)
    }

    pub fn try_desugar_with_names_and_effect(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
        effect_constraint: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        let effect = self.effect_context(effect_constraint).ok_or_else(|| {
            "`do` block can only appear in a function returning an effect constraint".to_string()
        })?;
        self.try_desugar_with_env(t, env, Some(&no_variants), Some(effect))
    }

    pub fn try_desugar_with_names_and_variant_resolver(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
        resolver: &impl Fn(&str) -> Option<VariantLookup<'bump>>,
    ) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_with_env(t, env, Some(resolver), None)
    }

    pub fn try_desugar_with_names_variant_resolver_and_effect(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
        resolver: &impl Fn(&str) -> Option<VariantLookup<'bump>>,
        effect_constraint: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        let effect = self.effect_context(effect_constraint).ok_or_else(|| {
            "`do` block can only appear in a function returning an effect constraint".to_string()
        })?;
        self.try_desugar_with_env(t, env, Some(resolver), Some(effect))
    }

    fn try_desugar_without_variant_resolver(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
    ) -> Result<&'bump Term<'bump>, String> {
        self.try_desugar_with_env(t, env, Some(&no_variants), None)
    }

    /// Recursive helper that carries a name stack `env` (innermost first).
    fn try_desugar_with_env<R>(
        &self,
        t: &'bump Term<'bump>,
        env: &[&'bump str],
        resolver: Option<&R>,
        effect: Option<EffectContext>,
    ) -> Result<&'bump Term<'bump>, String>
    where
        R: Fn(&str) -> Option<VariantLookup<'bump>>,
    {
        let desugared = match t {
            // ── Named → Var resolution ──
            Term::Named(name) => {
                if let Some(i) = env.iter().position(|n| *n == *name) {
                    self.arena.var(i)
                } else {
                    self.arena.global(name)
                }
            }

            // ── NamedLam → Lam conversion ──
            Term::NamedLam(name, body) => {
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                self.arena
                    .lam(self.try_desugar_with_env(body, &ext, resolver, None)?)
            }

            // ── Recurse into children ──
            Term::App(f, a) => self.arena.app(
                self.try_desugar_with_env(f, env, resolver, effect)?,
                self.try_desugar_with_env(a, env, resolver, effect)?,
            ),
            Term::Implicit(inner) => self
                .arena
                .implicit(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Lam(_) => {
                // Already-desugared Lam (from `def`): recurse into body with
                // a dummy binder since we don't know the name.
                // The body uses Var which already encodes binding, so just
                // recurse (Var indices are shifted appropriately by the Lam).
                t
            }
            Term::Pi(name, a, b) => {
                let a2 = self.try_desugar_with_env(a, env, resolver, effect)?;
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                let b2 = self.try_desugar_with_env(b, &ext, resolver, effect)?;
                self.arena.pi(name, a2, b2)
            }
            Term::Let(name, val, body, mc) => {
                let v2 = self.try_desugar_with_env(val, env, resolver, effect)?;
                let mc2 = mc
                    .map(|c| self.try_desugar_with_env(c, env, resolver, effect))
                    .transpose()?;
                let mut ext: Vec<&'bump str> = vec![*name];
                ext.extend_from_slice(env);
                let b2 = self.try_desugar_with_env(body, &ext, resolver, effect)?;
                self.arena.let_(name, v2, b2, mc2)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                let c2 = self.try_desugar_with_env(cond, env, resolver, effect)?;
                let t2 = self.try_desugar_with_env(tbranch, env, resolver, effect)?;
                let f2 = self.try_desugar_with_env(fbranch, env, resolver, effect)?;
                self.arena.if_then_else(c2, t2, f2)
            }
            Term::Annot(inner, c) => self.arena.annot(
                self.try_desugar_with_env(inner, env, resolver, effect)?,
                self.try_desugar_with_env(c, env, resolver, effect)?,
            ),
            Term::ByProof(inner, tactics) => {
                // Tactics contain terms that may have Named refs
                let inner2 = inner
                    .map(|i| self.try_desugar_with_env(i, env, resolver, effect))
                    .transpose()?;
                let tactics2: Vec<_> = tactics
                    .iter()
                    .map(|tac| {
                        Ok(match tac {
                            Tactic::Exact(t) => {
                                Tactic::Exact(self.try_desugar_with_env(t, env, resolver, effect)?)
                            }
                            Tactic::Apply(t) => {
                                Tactic::Apply(self.try_desugar_with_env(t, env, resolver, effect)?)
                            }
                            Tactic::Intro(n) => Tactic::Intro(*n),
                            Tactic::Have(n, t) => Tactic::Have(
                                n,
                                self.try_desugar_with_env(t, env, resolver, effect)?,
                            ),
                            Tactic::Custom(n, args) => {
                                let args = args
                                    .iter()
                                    .map(|arg| {
                                        self.try_desugar_with_env(arg, env, resolver, effect)
                                    })
                                    .collect::<Result<Vec<_>, _>>()?;
                                Tactic::Custom(n, self.arena.alloc_slice(&args))
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena
                    .by_proof(inner2, self.arena.alloc_slice(&tactics2))
            }
            Term::Refine(name, parent, p) => {
                let p2 = self.try_desugar_with_env(parent, env, resolver, effect)?;
                // Replace the refinement parameter reference with RefParam
                // BEFORE desugaring, so that prove_auto / subst_ref_param
                // can substitute the subject.  We must do this before
                // desugar_with_env because the latter could resolve
                // Named(name) to Var(i) if name shadows an outer binding.
                let pred_with_param = self.arena.map(p, &|node| {
                    if let Term::Named(n) = node
                        && *n == *name
                    {
                        return Some(self.arena.ref_param());
                    }
                    None
                });
                let pred2 = self.try_desugar_with_env(pred_with_param, env, resolver, effect)?;
                self.arena.refine(name, p2, pred2)
            }
            Term::EnumDef(name, variants) => {
                let variants2: Vec<_> = variants
                    .iter()
                    .map(|(variant_name, fields)| {
                        let fields2 = fields
                            .iter()
                            .map(|(field_name, constraint)| {
                                Ok((
                                    *field_name,
                                    self.try_desugar_with_env(constraint, env, resolver, effect)?,
                                ))
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        Ok((*variant_name, self.arena.alloc_slice(&fields2)))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena
                    .enum_def(name, self.arena.alloc_slice(&variants2))
            }
            Term::StructDef(name, fields) => {
                let fields2 = fields
                    .iter()
                    .map(|(field_name, constraint)| {
                        Ok((
                            *field_name,
                            self.try_desugar_with_env(constraint, env, resolver, effect)?,
                        ))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena
                    .struct_def(name, self.arena.alloc_slice(&fields2))
            }
            Term::Match(scrut, branches) => {
                let s2 = self.try_desugar_with_env(scrut, env, resolver, effect)?;
                let bs2: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let mut ext: Vec<&'bump str> = binds.iter().map(|(n, _)| *n).collect();
                        ext.extend_from_slice(env);
                        let b2 = self.try_desugar_with_env(body, &ext, resolver, effect)?;
                        let binds2: Vec<_> = binds
                            .iter()
                            .map(|(n, c)| {
                                Ok((*n, self.try_desugar_with_env(c, env, resolver, effect)?))
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        Ok((*idx, self.arena.alloc_slice(&binds2), b2))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena.match_(s2, self.arena.alloc_slice(&bs2))
            }
            Term::NamedMatch(scrut, branches) => {
                let s2 = self.try_desugar_with_env(scrut, env, resolver, effect)?;
                let resolver = resolver.ok_or_else(|| {
                    "cannot desugar named match without variant context".to_string()
                })?;
                let bs2: Vec<_> = branches
                    .iter()
                    .map(|(variant_name, binds, body)| {
                        let (_, idx, field_specs) = resolver(variant_name)
                            .ok_or_else(|| format!("unknown match variant: {}", variant_name))?;
                        let bind_specs: Vec<_> = binds
                            .iter()
                            .enumerate()
                            .map(|(i, (n, fallback))| {
                                let constraint =
                                    field_specs.get(i).map(|(_, c)| *c).unwrap_or(*fallback);
                                Ok((
                                    *n,
                                    self.try_desugar_with_env(
                                        constraint,
                                        env,
                                        Some(resolver),
                                        effect,
                                    )?,
                                ))
                            })
                            .collect::<Result<Vec<_>, String>>()?;
                        let mut ext: Vec<&'bump str> = binds.iter().map(|(n, _)| *n).collect();
                        ext.extend_from_slice(env);
                        let b2 = self.try_desugar_with_env(body, &ext, Some(resolver), effect)?;
                        Ok((idx, self.arena.alloc_slice(&bind_specs), b2))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena.match_(s2, self.arena.alloc_slice(&bs2))
            }
            Term::Variant(name, idx, payloads) => {
                let ps: Vec<_> = payloads
                    .iter()
                    .map(|p| self.try_desugar_with_env(p, env, resolver, effect))
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena.variant(name, *idx, self.arena.alloc_slice(&ps))
            }
            Term::StructCons(name, fields) => {
                let fs: Vec<_> = fields
                    .iter()
                    .map(|f| self.try_desugar_with_env(f, env, resolver, effect))
                    .collect::<Result<Vec<_>, String>>()?;
                self.arena.struct_cons(name, self.arena.alloc_slice(&fs))
            }
            Term::StructProj(subject, idx) => self.arena.struct_proj(
                self.try_desugar_with_env(subject, env, resolver, effect)?,
                *idx,
            ),
            Term::MethodCall(receiver, method) => self.arena.method_call(
                self.try_desugar_with_env(receiver, env, resolver, effect)?,
                method,
            ),
            Term::Do(stmts) => {
                let effect = effect.ok_or_else(|| {
                    "`do` block can only appear in a function returning an effect constraint"
                        .to_string()
                })?;
                self.desugar_do(stmts, env, resolver, effect)?
            }
            Term::Unsafe(inner) => self
                .arena
                .unsafe_(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Pure(inner) => self
                .arena
                .pure(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Quote(inner) => self
                .arena
                .quote(self.try_desugar_with_env(inner, env, resolver, effect)?),
            Term::Splice(inner) => self
                .arena
                .splice(self.try_desugar_with_env(inner, env, resolver, effect)?),

            // ── Leaf / no-name-binding nodes ──
            Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::Builtin(_)
            | Term::Global(_)
            | Term::AutoProof
            | Term::RefParam => t,
        };
        Ok(desugared)
    }

    fn desugar_do<R>(
        &self,
        stmts: &'bump [DoStmt<'bump>],
        env: &[&'bump str],
        resolver: Option<&R>,
        effect: EffectContext,
    ) -> Result<&'bump Term<'bump>, String>
    where
        R: Fn(&str) -> Option<VariantLookup<'bump>>,
    {
        let Some((last, prefix)) = stmts.split_last() else {
            return Err("do block must have at least one statement".to_string());
        };
        let mut ext_env = env.to_vec();
        for stmt in prefix {
            match stmt {
                DoStmt::Bind(name, _) | DoStmt::Let(name, _, _) => ext_env.insert(0, *name),
                DoStmt::Expr(_) => ext_env.insert(0, self.arena.alloc_str("_")),
            }
        }
        let mut body = match last {
            DoStmt::Expr(expr) => {
                self.try_desugar_with_env(expr, &ext_env, resolver, Some(effect))?
            }
            DoStmt::Let(..) | DoStmt::Bind(..) => {
                return Err("do block must end with a result expression".to_string());
            }
        };
        for stmt in prefix.iter().rev() {
            match stmt {
                DoStmt::Bind(name, rhs) => {
                    ext_env.remove(0);
                    let rhs = self.try_desugar_with_env(rhs, &ext_env, resolver, Some(effect))?;
                    body = self
                        .arena
                        .let_(name, rhs, body, Some(self.io_data_constraint()));
                }
                DoStmt::Let(name, rhs, mconstr) => {
                    ext_env.remove(0);
                    let rhs = self.try_desugar_with_env(rhs, &ext_env, resolver, Some(effect))?;
                    let c = mconstr
                        .map(|c| self.try_desugar_with_env(c, &ext_env, resolver, Some(effect)))
                        .transpose()?;
                    body = self.arena.let_(name, rhs, body, c);
                }
                DoStmt::Expr(expr) => {
                    ext_env.remove(0);
                    let expr = self.try_desugar_with_env(expr, &ext_env, resolver, Some(effect))?;
                    body = self.arena.let_(
                        self.arena.alloc_str("_"),
                        expr,
                        body,
                        Some(self.io_data_constraint()),
                    );
                }
            }
        }
        Ok(body)
    }

    fn effect_context(&self, constraint: &'bump Term<'bump>) -> Option<EffectContext> {
        self.effect_inner(constraint).map(|_| EffectContext)
    }

    fn effect_inner(&self, constraint: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        match constraint {
            Term::App(_, inner) => Some(inner),
            _ => None,
        }
    }

    fn io_data_constraint(&self) -> &'bump Term<'bump> {
        self.arena.app(
            self.arena.builtin(self.arena.alloc_str(BUILTIN_IO)),
            self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
        )
    }
}

fn no_variants<'bump>(_name: &str) -> Option<VariantLookup<'bump>> {
    None
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
            Term::Implicit(inner) => self.arena.implicit(recurse(inner, cutoff)),
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
                        Tactic::Custom(n, args) => {
                            let args = args
                                .iter()
                                .map(|arg| recurse(arg, cutoff))
                                .collect::<Vec<_>>();
                            Tactic::Custom(n, self.arena.alloc_slice(&args))
                        }
                    })
                    .collect();
                self.arena
                    .by_proof(inner_mapped, self.arena.alloc_slice(&mapped))
            }
            Term::Refine(n, par, p) => {
                self.arena
                    .refine(n, recurse(par, cutoff), recurse(p, cutoff))
            }
            Term::EnumDef(name, variants) => {
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
                self.arena.enum_def(name, self.arena.alloc_slice(&mapped))
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
            Term::MethodCall(receiver, method) => {
                self.arena.method_call(recurse(receiver, cutoff), method)
            }
            Term::Unsafe(inner) => self.arena.unsafe_(recurse(inner, cutoff)),
            Term::Pure(inner) => self.arena.pure(recurse(inner, cutoff)),
            Term::Quote(inner) => self.arena.quote(recurse(inner, cutoff)),
            Term::Splice(inner) => self.arena.splice(recurse(inner, cutoff)),
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
    /// This is used when checking application constraints, including
    /// `check_app` and Pi inference.
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
        Term::Implicit(inner) => arena.implicit(shift_term(arena, d, cutoff, inner)),
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
        Term::Unsafe(inner) => arena.unsafe_(shift_term(arena, d, cutoff, inner)),
        Term::Pure(inner) => arena.pure(shift_term(arena, d, cutoff, inner)),
        Term::MethodCall(receiver, method) => {
            arena.method_call(shift_term(arena, d, cutoff, receiver), method)
        }
        Term::Quote(inner) => arena.quote(shift_term(arena, d, cutoff, inner)),
        Term::Splice(inner) => arena.splice(shift_term(arena, d, cutoff, inner)),
        // All other nodes: return unchanged (no Var children that need shifting
        // beyond what's already covered by recursive cases, or leaf nodes).
        _ => t,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bumpalo::Bump;

    fn a() -> (&'static Bump, &'static TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        let arena = Box::leak(Box::new(TermArena::new(b)));
        (b, arena)
    }

    fn sub() -> (
        &'static Bump,
        &'static TermArena<'static>,
        SubstitutionContext<'static>,
    ) {
        let (b, arena) = a();
        (b, arena, SubstitutionContext::new(arena))
    }

    // ── shift ──

    #[test]
    fn shift_var_below_cutoff_unchanged() {
        let (_, arena, ctx) = sub();
        let t = ctx.shift(3, 1, arena.var(0));
        assert_eq!(*t, Term::Var(0));
    }

    #[test]
    fn shift_var_above_cutoff_adds_d() {
        let (_, arena, ctx) = sub();
        let t = ctx.shift(2, 0, arena.var(1));
        assert_eq!(*t, Term::Var(3));
    }

    #[test]
    fn shift_under_lam_bumps_cutoff() {
        let (_, arena, ctx) = sub();
        let lam = arena.lam(arena.var(0));
        let t = ctx.shift(1, 0, lam);
        assert_eq!(*t, *arena.lam(arena.var(0)));
    }

    #[test]
    fn shift_under_lam_bumps_var_1_to_2() {
        let (_, arena, ctx) = sub();
        let lam = arena.lam(arena.var(1));
        let t = ctx.shift(1, 0, lam);
        assert_eq!(*t, *arena.lam(arena.var(2)));
    }

    // ── subst ──

    #[test]
    fn subst_replaces_var() {
        let (_, arena, ctx) = sub();
        let t = ctx.subst(arena.lit_int(42), 0, arena.var(0));
        assert_eq!(*t, Term::LitInt(42));
    }

    #[test]
    fn subst_does_not_replace_other_var() {
        let (_, arena, ctx) = sub();
        let t = ctx.subst(arena.lit_int(42), 0, arena.var(1));
        assert_eq!(*t, Term::Var(1));
    }

    // ── beta ──

    #[test]
    fn beta_simple() {
        let (_, arena, ctx) = sub();
        let t = ctx.beta(arena.var(0), arena.lit_int(42));
        assert_eq!(*t, Term::LitInt(42));
    }

    #[test]
    fn beta_preserves_free_vars() {
        let (_, arena, ctx) = sub();
        let t = ctx.beta(arena.var(1), arena.lit_int(42));
        assert_eq!(*t, Term::Var(0));
    }

    // ── instantiate_pi ──

    #[test]
    fn instantiate_pi_replaces_var_0() {
        let (_, arena, ctx) = sub();
        let t = ctx.instantiate_pi(arena.lit_int(42), arena.var(0));
        assert_eq!(*t, Term::LitInt(42));
    }

    #[test]
    fn instantiate_pi_shifts_free_vars() {
        let (_, arena, ctx) = sub();
        let t = ctx.instantiate_pi(arena.lit_int(42), arena.var(1));
        assert_eq!(*t, Term::Var(0));
    }

    // ── Desugarer ──

    #[test]
    fn desugar_named_to_var() {
        let (_b, arena) = a();
        let desugarer = Desugarer::new(arena);
        let name = arena.alloc_str("x");
        let t = arena.named_lam(name, arena.named(name));
        let d = desugarer.desugar(t);
        assert_eq!(*d, *arena.lam(arena.var(0)));
    }

    #[test]
    fn desugar_nested_named() {
        let (_b, arena) = a();
        let desugarer = Desugarer::new(arena);
        let x = arena.alloc_str("x");
        let y = arena.alloc_str("y");
        let t = arena.named_lam(x, arena.named_lam(y, arena.named(x)));
        let d = desugarer.desugar(t);
        assert_eq!(*d, *arena.lam(arena.lam(arena.var(1))));
    }
}
