use crate::checker::builtin::classify_builtin;
use crate::checker::context::Context;
use crate::core::syntax::{Term, Universe};

pub struct Classifier;

impl Classifier {
    pub fn classify(ctx: &Context<'_>, t: &Term<'_>) -> Option<Universe> {
        match t {
            Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::Lam(_)
            | Term::PrimOp(_)
            | Term::RefParam => Some(Universe::UData),
            Term::App(f, _) => Self::classify(ctx, f),
            Term::Universe(u) => Some(*u),
            Term::AutoProof => Some(Universe::UProof),
            Term::Pi(_, _, _) | Term::Refine(_, _, _) => Some(Universe::UProp),
            Term::Var(i) => ctx.lookup(*i).and_then(|ty| Self::classify(ctx, ty)),
            Term::Annot(t, _) => Self::classify(ctx, t),
            Term::ByProof(Some(t), _) => Self::classify(ctx, t),
            Term::ByProof(None, _) => Some(Universe::UProof),
            Term::Let(_, _, body, _) => Self::classify(ctx, body),
            Term::IfThenElse(_, t, _) => Self::classify(ctx, t),
            Term::Builtin(name) => classify_builtin(name).or(Some(Universe::UData)),
            Term::UnionDef(..) => Some(Universe::UProp),
            Term::Variant(..) => Some(Universe::UData),
            Term::Match(_, branches) => {
                // Match type = type of first branch (all branches must agree)
                branches
                    .first()
                    .map(|(_, _, body)| Self::classify(ctx, body))
                    .flatten()
            }
        }
    }
}

pub fn classify(ctx: &Context<'_>, t: &Term<'_>) -> Option<Universe> {
    Classifier::classify(ctx, t)
}
