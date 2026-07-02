//! Shared semantic queries over terms.

use crate::checker::builtin::BuiltinRegistry;
use crate::checker::context::Context;
use crate::core::syntax::{Term, Universe};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    DataTop,
    MetaConstraint,
    BuiltinDataConstraint,
    Refine,
    Pi,
    UnionConstraint,
    StructConstraint,
    LogicalOp,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErasePolicy {
    KeepData,
    EraseToUnit,
    EraseToParent,
}

#[derive(Debug, Clone, Copy)]
pub struct SemanticQueries<'a> {
    builtins: &'a BuiltinRegistry,
}

impl<'a> SemanticQueries<'a> {
    pub fn new(builtins: &'a BuiltinRegistry) -> Self {
        Self { builtins }
    }

    pub fn universe(&self, ctx: &Context<'_>, term: &Term<'_>) -> Option<Universe> {
        match term {
            Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::Lam(_)
            | Term::PrimOp(_)
            | Term::RefParam => Some(Universe::UData),
            Term::App(f, _) => self.universe(ctx, f),
            Term::Implicit(inner) => self.universe(ctx, inner),
            Term::Universe(u) => Some(*u),
            Term::AutoProof => Some(Universe::UProof),
            Term::Pi(_, _, _) | Term::Refine(_, _, _) => Some(Universe::UProp),
            Term::Var(i) => ctx
                .lookup(*i)
                .and_then(|constraint| self.universe(ctx, constraint))
                .or(Some(Universe::UData)),
            Term::Annot(t, _) => self.universe(ctx, t),
            Term::Unsafe(inner) => self.universe(ctx, inner),
            Term::Pure(inner) => self.universe(ctx, inner),
            Term::ByProof(Some(t), _) => self.universe(ctx, t),
            Term::ByProof(None, _) => Some(Universe::UProof),
            Term::Let(_, _, body, _) => self.universe(ctx, body),
            Term::IfThenElse(_, t, _) => self.universe(ctx, t),
            Term::Builtin(name) | Term::Global(name) => {
                self.builtins.universe_of(name).or(Some(Universe::UData))
            }
            Term::UnionDef(..) => Some(Universe::UProp),
            Term::Variant(..) => Some(Universe::UData),
            Term::StructDef(..) => Some(Universe::UProp),
            Term::StructCons(..) => Some(Universe::UData),
            Term::StructProj(subject, _) => self.universe(ctx, subject),
            Term::Match(_, branches) => branches
                .first()
                .and_then(|(_, _, body)| self.universe(ctx, body)),
            Term::Named(_) | Term::NamedLam(..) | Term::NamedMatch(..) | Term::Do(_) => {
                panic!("parser-level term reached semantic query before desugaring")
            }
        }
    }

    pub fn constraint_kind(&self, term: &Term<'_>) -> ConstraintKind {
        match term {
            Term::Builtin(name) | Term::Global(name) if *name == "data" => ConstraintKind::DataTop,
            Term::Implicit(_) => ConstraintKind::MetaConstraint,
            Term::Builtin(name) | Term::Global(name)
                if matches!(*name, "prop" | "theorem" | "proof") =>
            {
                ConstraintKind::MetaConstraint
            }
            Term::Universe(Universe::UData) => ConstraintKind::DataTop,
            Term::Universe(_) => ConstraintKind::MetaConstraint,
            Term::Builtin(name) | Term::Global(name)
                if matches!(*name, "int" | "bool" | "str" | "ptr") =>
            {
                ConstraintKind::BuiltinDataConstraint
            }
            Term::App(head, _) if matches!(head, Term::Builtin(name) | Term::Global(name) if *name == "ptr") => {
                ConstraintKind::BuiltinDataConstraint
            }
            Term::Builtin(name) | Term::Global(name) if matches!(*name, "and" | "or" | "not") => {
                ConstraintKind::LogicalOp
            }
            Term::Refine(..) => ConstraintKind::Refine,
            Term::Pi(..) => ConstraintKind::Pi,
            Term::UnionDef(..) => ConstraintKind::UnionConstraint,
            Term::StructDef(..) => ConstraintKind::StructConstraint,
            _ => ConstraintKind::Unknown,
        }
    }

    pub fn is_meta_constraint(&self, term: &Term<'_>) -> bool {
        matches!(
            self.constraint_kind(term),
            ConstraintKind::DataTop | ConstraintKind::MetaConstraint
        )
    }

    pub fn is_erased_parameter_constraint(&self, term: &Term<'_>) -> bool {
        matches!(self.constraint_kind(term), ConstraintKind::MetaConstraint)
    }

    pub fn erase_policy(&self, term: &Term<'_>) -> ErasePolicy {
        match term {
            Term::Refine(..) => ErasePolicy::EraseToParent,
            Term::Implicit(inner) => self.erase_policy(inner),
            Term::Annot(inner, _) | Term::ByProof(Some(inner), _) => self.erase_policy(inner),
            Term::App(f, _) => self.data_policy(f),
            Term::Builtin(_) | Term::Global(_) => self.data_policy(term),
            Term::Named(_) | Term::NamedLam(..) | Term::NamedMatch(..) | Term::Do(_) => {
                panic!("parser-level term reached erase-policy query before desugaring")
            }
            Term::ByProof(None, _)
            | Term::AutoProof
            | Term::Pi(..)
            | Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof)
            | Term::UnionDef(..)
            | Term::StructDef(..) => ErasePolicy::EraseToUnit,
            _ => ErasePolicy::KeepData,
        }
    }

    fn data_policy(&self, term: &Term<'_>) -> ErasePolicy {
        if self.universe(&Context::empty(), term) == Some(Universe::UData) {
            ErasePolicy::KeepData
        } else {
            ErasePolicy::EraseToUnit
        }
    }
}
