//! Proof-search subroutines for `TypeChecker`.

use crate::checker::TypeChecker;
use crate::checker::context::Context;
use crate::config::{AND_ELIM_LEFT, AND_INTRO, BUILTIN_AND};
use crate::core::pool::TermArena;
use crate::core::syntax::{PrimOp, Tactic, Term};
use crate::diagnostic::Diagnostic;
use crate::pretty::PrettyPrinter;

macro_rules! diag {
    ($($arg:tt)*) => {
        Diagnostic::new(format!($($arg)*))
    };
}

/// Internal proof frame for tactic execution.
enum Frame<'bump> {
    AppFrame(&'bump Term<'bump>), // apply f  →  App(f, ·)
    LamFrame,                     // intro    →  Lam(·)
}

impl<'bump> TypeChecker<'bump> {
    // ── Tactic execution ──

    /// Build a proof term from a sequence of tactics, without checking.
    /// Returns `(proof_term, final_context)` where `proof_term` is the
    /// constructed proof (wrapped with intro/apply frames) and
    /// `final_context` includes any hypotheses introduced by `intro` and
    /// lemmas from `have`.
    pub(crate) fn build_proof_from_tactics(
        &self,
        ctx: &Context<'bump>,
        subject: Option<&'bump Term<'bump>>,
        goal: &'bump Term<'bump>,
        tactics: &'bump [Tactic<'bump>],
    ) -> Result<(&'bump Term<'bump>, Context<'bump>), Diagnostic> {
        let mut current_ctx = ctx.clone();
        let instantiated_goal = match subject {
            Some(s) => self.subst_ref_param(s, goal),
            None => goal,
        };
        let mut current_goal = instantiated_goal;
        let mut local_names: Vec<&'bump str> = Vec::new();
        let mut frames: Vec<Frame<'bump>> = Vec::new();

        let n = tactics.len();
        for (i, tactic) in tactics.iter().enumerate() {
            let is_last = i == n - 1;
            match tactic {
                Tactic::Exact(proof_term) => {
                    if !is_last {
                        return Err(Diagnostic::new(
                            "`exact` must be the last tactic in a proof block",
                        ));
                    }
                    let proof_term = self.desugar_with_names_context(proof_term, &local_names)?;
                    let full_proof = Self::wrap_frames(self.arena, proof_term, &frames);
                    return Ok((full_proof, current_ctx));
                }
                Tactic::Apply(f) => {
                    if is_last {
                        return Err(Diagnostic::new(
                            "`apply` cannot be the last tactic (use `exact`)",
                        ));
                    }
                    // Don't whnf f — that strips Annot which holds the type.
                    let f = self.desugar_with_names_context(f, &local_names)?;
                    let (dom, cod) = self.extract_pi_type(&current_ctx, f)?;
                    let goal_nf = self.evaluator.whnf(current_goal)?;
                    if !self.terms_compatible(cod, goal_nf) {
                        return Err(diag!(
                            "apply: function codomain {} does not match goal {}",
                            PrettyPrinter::pretty(cod),
                            PrettyPrinter::pretty(goal_nf)
                        ));
                    }
                    frames.push(Frame::AppFrame(f));
                    current_goal = dom;
                }
                Tactic::Intro(name) => {
                    if is_last {
                        return Err(Diagnostic::new(
                            "`intro` cannot be the last tactic (use `exact`)",
                        ));
                    }
                    let goal_nf = self.evaluator.whnf(current_goal)?;
                    match goal_nf {
                        Term::Pi(n, a_dom, b_cod) => {
                            let var_name = name.unwrap_or(n);
                            current_ctx = current_ctx.extend(var_name, a_dom);
                            local_names.insert(0, var_name);
                            frames.push(Frame::LamFrame);
                            current_goal = b_cod;
                        }
                        _ => {
                            return Err(diag!(
                                "intro: goal {} is not Pi",
                                PrettyPrinter::pretty(goal_nf)
                            ));
                        }
                    }
                }
                Tactic::Have(name, lemma) => {
                    if is_last {
                        return Err(Diagnostic::new(
                            "`have` cannot be the last tactic (use `exact`)",
                        ));
                    }
                    let lemma = self.desugar_with_names_context(lemma, &local_names)?;
                    let lemma_val = self.evaluator.whnf(lemma)?;
                    current_ctx = current_ctx.add_theorem(name, lemma_val);
                }
                Tactic::Custom(name, _) => {
                    return Err(Diagnostic::new(format!(
                        "custom tactic `{name}` reached checker before metaprogram expansion"
                    )));
                }
            }
        }

        Err(Diagnostic::new("Proof block must end with `exact`"))
    }

    /// Execute tactics and verify the resulting proof against the goal.
    pub(crate) fn execute_tactics(
        &self,
        ctx: &Context<'bump>,
        subject: Option<&'bump Term<'bump>>,
        goal: &'bump Term<'bump>,
        tactics: &'bump [Tactic<'bump>],
    ) -> Result<(), Diagnostic> {
        let (proof, final_ctx) = self.build_proof_from_tactics(ctx, subject, goal, tactics)?;
        // Evaluate the constructed proof term.
        let proof_val = self.evaluator.whnf(proof)?;
        match proof_val {
            Term::LitBool(true) => Ok(()),
            Term::LitBool(false) => Err(Diagnostic::new("Proof term evaluates to false")),
            _ => {
                // Non-boolean proof: check it against the instantiated goal.
                let instantiated_goal = match subject {
                    Some(s) => self.subst_ref_param(s, goal),
                    None => goal,
                };
                self.check(&final_ctx, proof, instantiated_goal)
            }
        }
    }

    /// Wrap a base proof term with accumulated frames.
    /// Frames are applied outermost-first → iterate in reverse.
    fn wrap_frames(
        arena: &'bump TermArena<'bump>,
        base: &'bump Term<'bump>,
        frames: &[Frame<'bump>],
    ) -> &'bump Term<'bump> {
        let mut proof = base;
        for frame in frames.iter().rev() {
            match frame {
                Frame::AppFrame(f) => proof = arena.app(f, proof),
                Frame::LamFrame => proof = arena.lam(proof),
            }
        }
        proof
    }

    /// Extract the Pi domain and codomain from a term, looking through
    /// annotations, context bindings, and named references.
    fn extract_pi_type(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
    ) -> Result<(&'bump Term<'bump>, &'bump Term<'bump>), Diagnostic> {
        // Direct annotation: `(body : Pi ...)`
        if let Term::Annot(_, ty) = t
            && let Some(pi) = Self::as_pi(ty)
        {
            return Ok(pi);
        }
        // Variable lookup
        if let Term::Var(i) = t
            && let Some(ty) = ctx.lookup(*i)
        {
            let ty_nf = self.evaluator.whnf(ty)?;
            if let Some(pi) = Self::as_pi(ty_nf) {
                return Ok(pi);
            }
        }
        Err(diag!(
            "apply: cannot infer Pi type for {}",
            PrettyPrinter::pretty(t)
        ))
    }

    fn as_pi(t: &'bump Term<'bump>) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
        if let Term::Pi(_, dom, cod) = t {
            Some((dom, cod))
        } else {
            None
        }
    }

    /// Check whether two terms are compatible (equal up to WHNF).
    fn terms_compatible(&self, t1: &'bump Term<'bump>, t2: &'bump Term<'bump>) -> bool {
        let Ok(v1) = self.evaluator.whnf(t1) else {
            return false;
        };
        let Ok(v2) = self.evaluator.whnf(t2) else {
            return false;
        };
        v1 == v2
    }

    // ── Proof search ──

    pub(crate) fn prove_auto(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        pred: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let instantiated = self.subst_ref_param(subject, pred);
        let instantiated_val = self.evaluator.whnf(instantiated)?;
        match instantiated_val {
            Term::LitBool(true) => Ok(()),
            Term::LitBool(false) => Err(diag!(
                "Refinement predicate does not hold: {} does not satisfy {}",
                PrettyPrinter::pretty(subject),
                PrettyPrinter::pretty(pred)
            )),
            _ if self.search_ctx_constraints(ctx, subject, pred) => Ok(()),
            _ if self.search_ctx(ctx, subject, pred) => Ok(()),
            _ => self.try_simple_derive(pred, ctx, subject),
        }
    }

    pub(crate) fn subst_ref_param(
        &self,
        subj: &'bump Term<'bump>,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if matches!(node, Term::RefParam) {
                Some(subj)
            } else {
                None
            }
        })
    }

    fn search_ctx(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        target: &'bump Term<'bump>,
    ) -> bool {
        ctx.iter()
            .flat_map(|entry| &entry.theorems)
            .any(|thm| self.eval_eq(subject, thm, target))
    }

    fn search_ctx_constraints(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        target: &'bump Term<'bump>,
    ) -> bool {
        let Term::Var(i) = subject else {
            return false;
        };
        let Some(constraint) = ctx.lookup(*i) else {
            return false;
        };
        let Ok(constraint) = self.evaluator.whnf(constraint) else {
            return false;
        };
        let Some(pred) = self.constraint_predicate(constraint) else {
            return false;
        };
        self.eval_eq(subject, pred, target)
    }

    fn constraint_predicate(&self, constraint: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        match constraint {
            Term::Refine(_, _, pred) => Some(pred),
            Term::Builtin(name) | Term::Global(name) => {
                crate::checker::context::lookup_refine(name, self.table()).map(|(_, pred)| pred)
            }
            _ => None,
        }
    }

    fn eval_eq(
        &self,
        subject: &'bump Term<'bump>,
        t1: &'bump Term<'bump>,
        t2: &'bump Term<'bump>,
    ) -> bool {
        let v1 = self.evaluator.whnf(self.subst_ref_param(subject, t1));
        let v2 = self.evaluator.whnf(self.subst_ref_param(subject, t2));
        matches!((v1, v2), (Ok(a), Ok(b)) if a == b)
    }

    fn try_simple_derive(
        &self,
        pred: &'bump Term<'bump>,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if self.try_derive_nonnegative_add(pred, ctx, subject) {
            return Ok(());
        }
        let Some((a, b)) = self.try_match_neq(pred) else {
            return Err(diag!(
                "Cannot automatically verify that {} satisfies {} — provide a manual proof with `by`",
                PrettyPrinter::pretty(subject),
                PrettyPrinter::pretty(pred)
            ));
        };
        let gt = self
            .arena
            .app(self.arena.app(self.arena.prim_op(PrimOp::Gt), a), b);
        let found = ctx
            .iter()
            .flat_map(|entry| &entry.theorems)
            .any(|thm| self.eval_eq_simple(gt, thm));
        if found {
            Ok(())
        } else {
            Err(diag!(
                "Cannot prove that {} satisfies {} (inequality cannot be derived from context)",
                PrettyPrinter::pretty(subject),
                PrettyPrinter::pretty(pred)
            ))
        }
    }

    fn try_derive_nonnegative_add(
        &self,
        pred: &'bump Term<'bump>,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
    ) -> bool {
        let Some((lhs, rhs)) = self.try_match_ge(pred) else {
            return false;
        };
        if !matches!(lhs, Term::RefParam) || !matches!(rhs, Term::LitInt(0)) {
            return false;
        }
        let Some((left, right)) = self.try_match_add(subject) else {
            return false;
        };
        if matches!(right, Term::LitInt(n) if *n >= 0) {
            return self.prove_auto(ctx, left, pred).is_ok();
        }
        if matches!(left, Term::LitInt(n) if *n >= 0) {
            return self.prove_auto(ctx, right, pred).is_ok();
        }
        false
    }

    fn try_match_ge(
        &self,
        t: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
        let Term::App(ge_app, b) = t else {
            return None;
        };
        let Term::App(prim, a) = *ge_app else {
            return None;
        };
        if !matches!(prim, Term::PrimOp(PrimOp::Ge)) {
            return None;
        }
        Some((a, b))
    }

    fn try_match_add(
        &self,
        t: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
        let Term::App(add_app, b) = t else {
            return None;
        };
        let Term::App(prim, a) = *add_app else {
            return None;
        };
        if !matches!(prim, Term::PrimOp(PrimOp::Add)) {
            return None;
        }
        Some((a, b))
    }

    fn try_match_neq(
        &self,
        t: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
        let Term::App(neq_app, b) = t else {
            return None;
        };
        let Term::App(prim, a) = *neq_app else {
            return None;
        };
        if !matches!(prim, Term::PrimOp(PrimOp::Neq)) {
            return None;
        }
        Some((a, b))
    }

    fn eval_eq_simple(&self, t1: &'bump Term<'bump>, t2: &'bump Term<'bump>) -> bool {
        matches!(
            (self.evaluator.whnf(t1), self.evaluator.whnf(t2)),
            (Ok(a), Ok(b)) if a == b
        )
    }

    #[allow(dead_code)]
    pub(crate) fn try_split_conj_proof<'t>(
        &self,
        goal: &'t Term<'t>,
        proof: &'t Term<'t>,
    ) -> Option<(&'t Term<'t>, &'t Term<'t>, &'t Term<'t>, &'t Term<'t>)> {
        let Term::App(and_app, b) = goal else {
            return None;
        };
        let Term::App(builtin, a) = *and_app else {
            return None;
        };
        let (Term::Builtin(name) | Term::Global(name)) = *builtin else {
            return None;
        };
        if *name != BUILTIN_AND {
            return None;
        }

        let Term::App(and_intro, pb) = proof else {
            return None;
        };
        let Term::App(builtin2, pa) = *and_intro else {
            return None;
        };
        let (Term::Builtin(n2) | Term::Global(n2)) = *builtin2 else {
            return None;
        };
        if *n2 != AND_INTRO {
            return None;
        }

        Some((a, pa, b, pb))
    }

    #[allow(dead_code)]
    pub(crate) fn prove_with(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        goal: &'bump Term<'bump>,
        proof: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if let Some((a, pa, b, pb)) = self.try_split_conj_proof(goal, proof) {
            self.prove_with(ctx, subject, a, pa)?;
            return self.prove_with(ctx, subject, b, pb);
        }

        match proof {
            Term::Builtin(name) | Term::Global(name) if *name == AND_ELIM_LEFT => Ok(()),
            Term::LitBool(true) => Ok(()),
            Term::AutoProof => self.prove_auto(ctx, subject, goal),
            _ => Err(Diagnostic::new(
                "This expression cannot be used as a proof — expected a proof term or `by` block",
            )),
        }
    }
}
