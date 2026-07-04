use std::collections::HashSet;

use crate::checker::context::empty_ctx;
use crate::config;
use crate::core::semantics::SemanticQueries;
use crate::core::syntax::Universe;
use crate::core::syntax::{DoStmt, Name, Tactic, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::Attribute;

use super::Compiler;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TerminationSource {
    User,
    Compiler,
    Extern,
    Unverified,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TerminationInfo {
    pub(crate) source: TerminationSource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TerminationClaim<'bump> {
    None,
    UserContract,
    UserProof(&'bump Term<'bump>),
}

impl<'bump> TerminationClaim<'bump> {
    pub(crate) fn is_user_claim(self) -> bool {
        !matches!(self, TerminationClaim::None)
    }

    pub(crate) fn merge(self, other: Self) -> Self {
        if other.is_user_claim() { other } else { self }
    }
}

impl TerminationInfo {
    pub(crate) fn certified(self) -> bool {
        !matches!(self.source, TerminationSource::Unverified)
    }
}

impl<'bump> Compiler<'bump> {
    pub(crate) fn mark_extern_terminating(&mut self, name: Name<'bump>) {
        self.termination.insert(
            name,
            TerminationInfo {
                source: TerminationSource::Extern,
            },
        );
    }

    pub(crate) fn record_data_termination(
        &mut self,
        name: Name<'bump>,
        body: &'bump Term<'bump>,
        claim: TerminationClaim<'bump>,
    ) {
        let source = if claim.is_user_claim() {
            TerminationSource::User
        } else if self.proves_terminating(name, body) {
            TerminationSource::Compiler
        } else {
            TerminationSource::Unverified
        };
        self.termination.insert(name, TerminationInfo { source });
    }

    pub(crate) fn termination_claim_from_attrs(
        &self,
        attrs: &[Attribute<'bump>],
        span: std::ops::Range<usize>,
    ) -> Result<TerminationClaim<'bump>, Diagnostic> {
        let Some(attr) = attrs
            .iter()
            .find(|attr| attr.is_name(config::TERMINATING_ATTR))
        else {
            return Ok(TerminationClaim::None);
        };

        match attr.args {
            [] => Ok(TerminationClaim::UserContract),
            [proof] => Ok(TerminationClaim::UserProof(proof)),
            _ => Err(Diagnostic::with_span(
                format!(
                    "#[{}] accepts at most one manual proof argument",
                    config::TERMINATING_ATTR
                ),
                span,
            )),
        }
    }

    pub(crate) fn verify_termination_claim(
        &self,
        claim: TerminationClaim<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        let TerminationClaim::UserProof(proof) = claim else {
            return Ok(());
        };
        let resolved = self.try_resolve_all(proof)?;
        let semantics = SemanticQueries::new(self.checker.builtins());
        if semantics.universe(&empty_ctx(), resolved) != Some(Universe::UProof) {
            return Err(Diagnostic::with_span(
                "termination proof check failed: expected a proof term",
                span,
            ));
        }
        let proof_constraint = self
            .arena
            .builtin(self.arena.alloc_str(config::BUILTIN_PROOF));
        self.checker
            .check(&empty_ctx(), resolved, proof_constraint)
            .map_err(|err| {
                Self::wrap_diagnostic("termination proof check failed", err, span.clone())
            })
    }

    pub(crate) fn ensure_logic_data_refs_terminate(
        &self,
        term: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        let mut refs = HashSet::new();
        collect_global_refs(term, &mut refs);
        let mut failures = refs
            .into_iter()
            .filter(|name| !config::is_std_intrinsic_name(name))
            .filter(|name| {
                self.termination
                    .get(*name)
                    .is_some_and(|info| !info.certified())
            })
            .collect::<Vec<_>>();
        failures.sort();
        if failures.is_empty() {
            return Ok(());
        }
        Err(Diagnostic::with_span(
            format!(
                "logic term references data definition(s) without a termination proof: {}. \
Use #[{}(<proof>)] to provide a manual termination proof, #[{}] to provide a termination contract, or rewrite the definition so the compiler can prove it terminates",
                failures.join(", "),
                config::TERMINATING_ATTR,
                config::TERMINATING_ATTR
            ),
            span,
        ))
    }

    fn proves_terminating(&self, name: Name<'bump>, body: &'bump Term<'bump>) -> bool {
        let runtime = runtime_body(body);
        let mut refs = HashSet::new();
        collect_global_refs(runtime, &mut refs);
        if refs.contains(name) {
            return false;
        }
        refs.into_iter().all(|dep| {
            config::is_std_intrinsic_name(dep)
                || self
                    .termination
                    .get(dep)
                    .map(|info| info.certified())
                    .unwrap_or(true)
        })
    }
}

fn runtime_body<'bump>(term: &'bump Term<'bump>) -> &'bump Term<'bump> {
    match term {
        Term::Annot(inner, _) => runtime_body(inner),
        Term::Lam(body) | Term::NamedLam(_, body) => runtime_body(body),
        Term::Unsafe(inner) | Term::Pure(inner) => runtime_body(inner),
        _ => term,
    }
}

fn collect_global_refs<'bump>(term: &'bump Term<'bump>, refs: &mut HashSet<Name<'bump>>) {
    match term {
        Term::Builtin(name) | Term::Global(name) | Term::Named(name) => {
            refs.insert(*name);
        }
        Term::App(f, a) => {
            collect_global_refs(f, refs);
            collect_global_refs(a, refs);
        }
        Term::Implicit(inner)
        | Term::Lam(inner)
        | Term::NamedLam(_, inner)
        | Term::Unsafe(inner)
        | Term::Pure(inner)
        | Term::Quote(inner)
        | Term::Splice(inner) => collect_global_refs(inner, refs),
        Term::Pi(_, a, b) => {
            collect_global_refs(a, refs);
            collect_global_refs(b, refs);
        }
        Term::Let(_, value, body, constraint) => {
            collect_global_refs(value, refs);
            collect_global_refs(body, refs);
            if let Some(constraint) = constraint {
                collect_global_refs(constraint, refs);
            }
        }
        Term::IfThenElse(cond, then_branch, else_branch) => {
            collect_global_refs(cond, refs);
            collect_global_refs(then_branch, refs);
            collect_global_refs(else_branch, refs);
        }
        Term::Refine(_, parent, predicate) | Term::Annot(parent, predicate) => {
            collect_global_refs(parent, refs);
            collect_global_refs(predicate, refs);
        }
        Term::ByProof(subject, tactics) => {
            if let Some(subject) = subject {
                collect_global_refs(subject, refs);
            }
            for tactic in *tactics {
                match tactic {
                    Tactic::Exact(t) | Tactic::Apply(t) | Tactic::Have(_, t) => {
                        collect_global_refs(t, refs)
                    }
                    Tactic::Intro(_) => {}
                    Tactic::Custom(_, args) => {
                        for arg in *args {
                            collect_global_refs(arg, refs);
                        }
                    }
                }
            }
        }
        Term::EnumDef(_, variants) => {
            for (_, fields) in *variants {
                for (_, constraint) in *fields {
                    collect_global_refs(constraint, refs);
                }
            }
        }
        Term::Variant(_, _, payloads) | Term::StructCons(_, payloads) => {
            for payload in *payloads {
                collect_global_refs(payload, refs);
            }
        }
        Term::Match(scrutinee, branches) => {
            collect_global_refs(scrutinee, refs);
            for (_, binds, body) in *branches {
                for (_, constraint) in *binds {
                    collect_global_refs(constraint, refs);
                }
                collect_global_refs(body, refs);
            }
        }
        Term::NamedMatch(scrutinee, branches) => {
            collect_global_refs(scrutinee, refs);
            for (_, binds, body) in *branches {
                for (_, constraint) in *binds {
                    collect_global_refs(constraint, refs);
                }
                collect_global_refs(body, refs);
            }
        }
        Term::Do(stmts) => {
            for stmt in *stmts {
                match stmt {
                    DoStmt::Bind(_, rhs) | DoStmt::Expr(rhs) => collect_global_refs(rhs, refs),
                    DoStmt::Let(_, rhs, constraint) => {
                        collect_global_refs(rhs, refs);
                        if let Some(constraint) = constraint {
                            collect_global_refs(constraint, refs);
                        }
                    }
                }
            }
        }
        Term::StructDef(_, fields) => {
            for (_, constraint) in *fields {
                collect_global_refs(constraint, refs);
            }
        }
        Term::StructProj(subject, _) | Term::MethodCall(subject, _) => {
            collect_global_refs(subject, refs);
        }
        Term::Var(_)
        | Term::LitInt(_)
        | Term::LitBool(_)
        | Term::LitStr(_)
        | Term::PrimOp(_)
        | Term::Universe(_)
        | Term::AutoProof
        | Term::RefParam => {}
    }
}
