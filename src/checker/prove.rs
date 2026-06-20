//! Proof-search subroutines for `TypeChecker`.

use crate::checker::TypeChecker;
use crate::checker::context::Context;
use crate::config::{AND_ELIM_LEFT, AND_INTRO, BUILTIN_AND};
use crate::core::syntax::{PrimOp, Term};
use crate::pretty::PrettyPrinter;

impl<'bump> TypeChecker<'bump> {
    // ── Proof search ──

    pub(crate) fn prove_auto(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        pred: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let instantiated = self.subst_ref_param(subject, pred);
        let instantiated_val = self.evaluator.whnf(instantiated)?;
        match instantiated_val {
            Term::LitBool(true) => Ok(()),
            Term::LitBool(false) => Err(format!(
                "Refinement predicate does not hold: {} does not satisfy {}",
                PrettyPrinter::pretty(subject),
                PrettyPrinter::pretty(pred)
            )),
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
    ) -> Result<(), String> {
        let Some((a, b)) = self.try_match_neq(pred) else {
            return Err(format!(
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
            Err(format!(
                "Cannot prove that {} satisfies {} (inequality cannot be derived from context)",
                PrettyPrinter::pretty(subject),
                PrettyPrinter::pretty(pred)
            ))
        }
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
        let Term::Builtin(name) = *builtin else {
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
        let Term::Builtin(n2) = *builtin2 else {
            return None;
        };
        if *n2 != AND_INTRO {
            return None;
        }

        Some((a, pa, b, pb))
    }

    pub(crate) fn prove_with(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        goal: &'bump Term<'bump>,
        proof: &'bump Term<'bump>,
    ) -> Result<(), String> {
        if let Some((a, pa, b, pb)) = self.try_split_conj_proof(goal, proof) {
            self.prove_with(ctx, subject, a, pa)?;
            return self.prove_with(ctx, subject, b, pb);
        }

        match proof {
            Term::Builtin(name) if *name == AND_ELIM_LEFT => Ok(()),
            Term::LitBool(true) => Ok(()),
            Term::AutoProof => self.prove_auto(ctx, subject, goal),
            Term::ProofBlock(inner) => self.prove_with(ctx, subject, goal, inner),
            _ => Err(
                "This expression cannot be used as a proof — expected a proof term or `by` block"
                    .to_string(),
            ),
        }
    }
}
