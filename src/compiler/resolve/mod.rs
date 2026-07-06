//! Name resolution and substitution passes.
//!
//! Functions that walk the AST to resolve `Builtin`/`Named` references
//! to their definitions, convert variant/struct constructor applications,
//! and perform top-level substitution.

use crate::checker::context::Context;
use crate::config::BUILTIN_INT;
use crate::core::syntax::{DoStmt, Name, PrimOp, Tactic, Term};
use crate::diagnostic::Diagnostic;

mod literals;
mod methods;

/// Result of collecting variant constructor args: (enum_name, variant_index, field_specs, args).
pub type VariantWithArgs<'bump> = (
    Name<'bump>,
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    Vec<&'bump Term<'bump>>,
);

/// Result of collecting struct constructor args: (struct_name, field_specs, args).
pub type StructWithArgs<'bump> = (
    Name<'bump>,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    Vec<&'bump Term<'bump>>,
);

use super::Compiler;

#[derive(Clone, Copy)]
pub(crate) struct MethodScopeEntry<'bump> {
    pub name: Name<'bump>,
    pub constraint: Option<&'bump Term<'bump>>,
}

impl<'bump> Compiler<'bump> {
    /// Resolve ALL free `Builtin(name)`/`Named(name)` references from the env
    /// (constants AND functions). Used for eval paths where function bodies
    /// need to be available.
    ///
    /// Local binders must become de Bruijn indices before global substitution,
    /// otherwise a global definition named `x` could capture `fun x => ...`.
    pub fn resolve_all(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.try_resolve_all(term)
            .expect("resolve_all failed; use try_resolve_all for parser terms")
    }

    pub fn try_resolve_all(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        self.try_resolve_all_with_expected(term, None)
    }

    pub(crate) fn try_resolve_all_with_expected(
        &self,
        term: &'bump Term<'bump>,
        expected: Option<&'bump Term<'bump>>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let term = self.rewrite_method_calls(term, &mut Vec::new())?;
        let term = self.checker.desugar_with_context(term)?;
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t
                && !crate::config::is_std_intrinsic_name(name)
                && let Some(def) = self.env.get(name)
            {
                return Some(def);
            }
            None
        });
        let t = self.elaborate_implicit_apps(t)?;
        // Also resolve variant apps, struct constructors, and zero-arg constructors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        let t = self.fold_struct_projections(t);
        let t = self.arena.map(t, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
                    && field_specs.is_empty()
                {
                    return Some(self.arena.variant(uname, idx, &[]));
                }
                // Zero-arg struct constructor
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
                    && fields.is_empty()
                {
                    return Some(self.arena.struct_cons(sname, &[]));
                }
                // Struct projector
                if let Some(_idx) = self.checker.lookup_struct_proj(name) {
                    // Can't resolve without subject — leave as-is
                }
            }
            None
        });
        let t = self.fold_struct_projections(t);
        self.elaborate_of_nat_literals(t, &Context::empty(), expected)
    }

    pub(crate) fn resolve_instance_value(
        &self,
        term: &'bump Term<'bump>,
        expected: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let term = self.rewrite_method_calls(term, &mut Vec::new())?;
        let term = self.checker.desugar_with_context(term)?;
        let term = self.elaborate_implicit_apps(term)?;
        let term = self.resolve_variant_apps(term);
        let term = self.resolve_struct_ctors(term);
        let term = self.resolve_struct_projs(term);
        let term = self.fold_struct_projections(term);
        self.elaborate_of_nat_literals(term, &Context::empty(), Some(expected))
    }

    /// Extract the function name from a term if it's a recursive call.
    /// Only returns `Some(name)` if the head is a `Builtin(name)` that
    /// maps to a function (i.e., has `Lam` body) in the env.
    pub fn extract_func_name(&self, term: &'bump Term<'bump>) -> Option<Name<'bump>> {
        let mut head = term;
        while let Term::App(f, _) = head {
            head = f;
        }
        if let Term::Builtin(name) | Term::Global(name) = head
            && let Some(def) = self.env.get(name)
        {
            if def.is_constant() {
                return None; // constants don't need self-reference
            }
            return Some(name);
        }
        None
    }

    /// Substitute known top-level definitions into a term (O(1) lookup).
    /// Also resolves variant/struct constructors to their term forms.
    /// Uses `is_constant()` to distinguish constants from functions.
    pub fn subst_top_level(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // First pass: resolve env lookups for constants only
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t
                && !crate::config::is_std_intrinsic_name(name)
                && let Some(def) = self.env.get(name)
                && def.is_constant()
            {
                return Some(def);
            }
            None
        });
        let t = self.elaborate_implicit_apps(t).unwrap_or(t);
        // Second pass: resolve variant apps, struct constructors, and projectors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        let t = self.fold_struct_projections(t);
        // Third pass: resolve remaining zero-arg variant/struct constructors
        let t = self.arena.map(t, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
                    && field_specs.is_empty()
                {
                    return Some(self.arena.variant(uname, idx, &[]));
                }
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
                    && fields.is_empty()
                {
                    return Some(self.arena.struct_cons(sname, &[]));
                }
            }
            None
        });
        self.fold_struct_projections(t)
    }

    fn elaborate_implicit_apps(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        match term {
            Term::App(f, a) => {
                let f = self.elaborate_implicit_apps(f)?;
                let a = self.elaborate_implicit_apps(a)?;
                let f = self.apply_pending_implicits_for_arg(f, a)?;
                Ok(self.arena.app(f, a))
            }
            Term::Let(n, v, b, mc) => {
                let v = self.elaborate_implicit_apps(v)?;
                let b = self.elaborate_implicit_apps(b)?;
                let mc = mc.map(|c| self.elaborate_implicit_apps(c)).transpose()?;
                Ok(self.arena.let_(n, v, b, mc))
            }
            Term::Lam(body) => Ok(self.arena.lam(self.elaborate_implicit_apps(body)?)),
            Term::Pi(n, a, b) => Ok(self.arena.pi(
                n,
                self.elaborate_implicit_apps(a)?,
                self.elaborate_implicit_apps(b)?,
            )),
            Term::IfThenElse(c, t, e) => Ok(self.arena.if_then_else(
                self.elaborate_implicit_apps(c)?,
                self.elaborate_implicit_apps(t)?,
                self.elaborate_implicit_apps(e)?,
            )),
            Term::Annot(inner, c) => Ok(self.arena.annot(
                self.elaborate_implicit_apps(inner)?,
                self.elaborate_implicit_apps(c)?,
            )),
            Term::Unsafe(inner) => Ok(self.arena.unsafe_(self.elaborate_implicit_apps(inner)?)),
            Term::Pure(inner) => Ok(self.arena.pure(self.elaborate_implicit_apps(inner)?)),
            Term::StructCons(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|f| self.elaborate_implicit_apps(f))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self
                    .arena
                    .struct_cons(name, self.arena.alloc_slice(&fields)))
            }
            Term::StructProj(subject, idx) => Ok(self
                .arena
                .struct_proj(self.elaborate_implicit_apps(subject)?, *idx)),
            Term::Variant(name, idx, payloads) => {
                let payloads = payloads
                    .iter()
                    .map(|p| self.elaborate_implicit_apps(p))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self
                    .arena
                    .variant(name, *idx, self.arena.alloc_slice(&payloads)))
            }
            Term::Match(scrut, branches) => {
                let scrut = self.elaborate_implicit_apps(scrut)?;
                let branches = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        Ok((*idx, *binds, self.elaborate_implicit_apps(body)?))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                Ok(self.arena.match_(scrut, self.arena.alloc_slice(&branches)))
            }
            Term::Quote(inner) => Ok(self.arena.quote(inner)),
            Term::Splice(inner) => Ok(self.arena.splice(self.elaborate_implicit_apps(inner)?)),
            _ => Ok(term),
        }
    }

    fn apply_pending_implicits_for_arg(
        &self,
        mut f: &'bump Term<'bump>,
        explicit_arg: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        while let Some(domain) = self.leading_implicit_domain(f)? {
            if self.is_implicit_meta_constraint(domain) {
                if self.is_explicit_constraint_arg(explicit_arg) {
                    break;
                }
                if let Some(inferred) = self.infer_elab_constraint(explicit_arg) {
                    f = self.arena.app(f, inferred);
                    continue;
                }
            }
            let Some((_, instance)) = self.checker.lookup_instance(domain)? else {
                return Err(Diagnostic::new(format!(
                    "missing implicit instance for {}",
                    crate::pretty::PrettyPrinter::pretty(
                        crate::checker::TypeChecker::implicit_inner(domain)
                    )
                )));
            };
            f = self.arena.app(f, instance);
        }
        Ok(f)
    }

    fn is_explicit_constraint_arg(&self, term: &'bump Term<'bump>) -> bool {
        matches!(
            term,
            Term::Builtin(_)
                | Term::Global(_)
                | Term::Universe(_)
                | Term::EnumDef(..)
                | Term::StructDef(..)
        ) || matches!(term, Term::App(head, _) if self.is_explicit_constraint_arg(head))
    }

    fn leading_implicit_domain(
        &self,
        f: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        let Some(sig) = self.infer_app_signature(f)? else {
            return Ok(None);
        };
        let sig = self.checker.evaluator.whnf(sig)?;
        if let Term::Pi(_, domain, _) = sig
            && crate::checker::TypeChecker::is_implicit_constraint(domain)
        {
            return Ok(Some(domain));
        }
        Ok(None)
    }

    fn infer_app_signature(
        &self,
        f: &'bump Term<'bump>,
    ) -> Result<Option<&'bump Term<'bump>>, Diagnostic> {
        match f {
            Term::Annot(_, sig) => Ok(Some(sig)),
            Term::Builtin(name) | Term::Global(name) => Ok(self.env.get(name).and_then(|def| {
                if let Term::Annot(_, sig) = def {
                    Some(*sig)
                } else {
                    None
                }
            })),
            Term::App(inner, arg) => {
                let Some(sig) = self.infer_app_signature(inner)? else {
                    return Ok(None);
                };
                let sig = self.checker.evaluator.whnf(sig)?;
                if let Term::Pi(_, _, codomain) = sig {
                    let sub = crate::core::debruijn::SubstitutionContext::new(self.arena);
                    Ok(Some(sub.instantiate_pi(arg, codomain)))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    fn is_implicit_meta_constraint(&self, term: &'bump Term<'bump>) -> bool {
        let Ok(inner) = self
            .checker
            .evaluator
            .whnf(crate::checker::TypeChecker::implicit_inner(term))
        else {
            return false;
        };
        matches!(
            inner,
            Term::Builtin(name) | Term::Global(name)
                if matches!(
                    crate::config::canonical_builtin_name(name),
                    "prop" | "theorem" | "proof" | "data"
                )
        ) || matches!(
            inner,
            Term::Universe(
                crate::core::syntax::Universe::UProp
                    | crate::core::syntax::Universe::UTheorem
                    | crate::core::syntax::Universe::UProof
                    | crate::core::syntax::Universe::UData
            )
        )
    }

    fn infer_elab_constraint(&self, term: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        match term {
            Term::Annot(_, constraint) => Some(constraint),
            Term::LitInt(_) => Some(self.arena.builtin(self.arena.alloc_str("int"))),
            Term::LitBool(_) => Some(self.arena.builtin(self.arena.alloc_str("bool"))),
            Term::LitStr(_) => Some(self.arena.builtin(self.arena.alloc_str("str"))),
            Term::StructCons(name, _) | Term::Variant(name, _, _) => Some(self.arena.builtin(name)),
            Term::Builtin(name) | Term::Global(name) => self.env.get(name).and_then(|def| {
                if let Term::Annot(_, constraint) = def {
                    Some(*constraint)
                } else {
                    None
                }
            }),
            _ => None,
        }
    }

}
