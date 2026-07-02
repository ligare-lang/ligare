//! Name resolution and substitution passes.
//!
//! Functions that walk the AST to resolve `Builtin`/`Named` references
//! to their definitions, convert variant/struct constructor applications,
//! and perform top-level substitution.

use crate::core::syntax::{Name, Term};
use crate::diagnostic::Diagnostic;

/// Result of collecting variant constructor args: (union_name, variant_index, field_specs, args).
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
        let term = self.checker.desugar_with_context(term)?;
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t
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
        Ok(self.fold_struct_projections(t))
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
            _ => Ok(term),
        }
    }

    fn apply_pending_implicits_for_arg(
        &self,
        mut f: &'bump Term<'bump>,
        explicit_arg: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        while let Some(domain) = self.leading_implicit_domain(f)? {
            if self.is_implicit_meta_constraint(domain)
                && let Some(inferred) = self.infer_elab_constraint(explicit_arg)
            {
                f = self.arena.app(f, inferred);
                continue;
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
                if matches!(*name, "prop" | "theorem" | "proof" | "data")
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

    pub(crate) fn fold_struct_projections(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::StructProj(subject, idx) = node
                && let Term::StructCons(_, values) = subject
                && values.iter().any(|value| Self::is_dictionary_field(value))
            {
                return values.get(*idx).copied();
            }
            None
        })
    }

    fn is_dictionary_field(term: &Term<'_>) -> bool {
        match term {
            Term::Lam(_) => true,
            Term::Annot(inner, constraint) => {
                matches!(constraint, Term::Pi(..)) || Self::is_dictionary_field(inner)
            }
            Term::Builtin(_) | Term::Global(_) => true,
            _ => false,
        }
    }

    /// Convert `App*(Builtin(name), args...)` to `Variant(union, idx, args)`.
    pub fn resolve_variant_apps(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // Try top-level first
        if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(t)
            && args.len() == field_specs.len()
        {
            let v = self
                .arena
                .variant(uname, idx, self.arena.alloc_slice(&args));
            // Recurse into payload to resolve nested constructors
            return self.resolve_variant_apps(v);
        }
        self.arena.map(t, &|node| {
            if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(node)
                && args.len() == field_specs.len()
            {
                let v = self
                    .arena
                    .variant(uname, idx, self.arena.alloc_slice(&args));
                return Some(self.resolve_variant_apps(v));
            }
            None
        })
    }

    /// Unwrap an App chain to find a variant constructor and collect its args.
    pub fn collect_variant_args(&self, t: &'bump Term<'bump>) -> Option<VariantWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Global(name) = current
            && let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
        {
            return Some((uname, idx, field_specs, args));
        }
        None
    }

    /// Convert `App*(Named("name.mk"), args...)` to `StructCons(name, args)`.
    pub fn resolve_struct_ctors(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Some((sname, field_specs, args)) = self.collect_struct_args(t)
            && args.len() == field_specs.len()
        {
            let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
            return self.resolve_struct_ctors(sc);
        }
        self.arena.map(t, &|node| {
            if let Some((sname, field_specs, args)) = self.collect_struct_args(node)
                && args.len() == field_specs.len()
            {
                let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
                return Some(self.resolve_struct_ctors(sc));
            }
            None
        })
    }

    /// Unwrap an App chain to find a struct constructor (Name.mk) and collect its args.
    pub fn collect_struct_args(&self, t: &'bump Term<'bump>) -> Option<StructWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Global(name) = current
            && let Some((sname, field_specs)) = self.checker.lookup_struct_ctor(name)
        {
            return Some((sname, field_specs, args));
        }
        None
    }

    /// Convert `App(Builtin("Name.field"), arg)` to `StructProj(arg, idx)`.
    pub fn resolve_struct_projs(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::App(f, arg) = node
                && let Term::Builtin(name) | Term::Global(name) = f
                && let Some(idx) = self.checker.lookup_struct_proj(name)
            {
                let arg = self.resolve_struct_ctors(self.resolve_struct_projs(arg));
                return Some(self.arena.struct_proj(arg, idx));
            }
            None
        })
    }
}
