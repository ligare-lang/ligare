//! Compiler orchestrator — coordinates parsing, constraint checking, and code generation.
//!
//! Resolution logic lives in `resolve.rs`; this module holds the `Compiler`
//! struct and its lifecycle methods.

pub mod cache;
mod meta;
pub mod modules;
mod pipeline;
mod resolve;
mod termination;

use std::collections::HashMap;
use std::fs;

use bumpalo::Bump;

use crate::backend::ir::FunSig;
use crate::checker::context::empty_ctx;
use crate::checker::{CheckMode, TypeChecker};
use crate::config::{
    BUILTIN_DATA, BUILTIN_PROOF, BUILTIN_PROP, BUILTIN_THEOREM, COMPILER_BUILTIN_ATTRIBUTE_ATTR,
    COMPILER_INTRINSIC_ATTR, CUSTOM_ATTRIBUTE_ATTR, GLOBAL_ALLOCATOR_NAME_PREFIX, TACTIC_ATTR,
    canonical_builtin_name,
};
use crate::core::eval::Evaluator;
use crate::core::pool::TermArena;
use crate::core::semantics::SemanticQueries;
use crate::core::syntax::{Name, PrimOp, Term, Universe};
use crate::diagnostic::Diagnostic;
use crate::front::parser::{TopLevel, parse_expr_top, parse_program};
use crate::pretty::PrettyPrinter;

mod monomorph;
use termination::TerminationClaim;

pub(crate) use pipeline::{CodegenState, MonomorphizedProgram};

fn read_source_file(file: &str) -> Result<String, Diagnostic> {
    fs::read_to_string(file)
        .map_err(|e| Diagnostic::new(format!("cannot read source file `{}`: {}", file, e)))
}

/// Borrowed view of the data C codegen needs.
///
/// This is intentionally a light wrapper over the existing compiler-owned
/// storage. It makes the handoff explicit without introducing a full pipeline
/// of separate IR types.
pub struct CodegenInput<'a, 'bump> {
    pub tops: &'a [TopLevel<'bump>],
    pub raw_defs: &'a [TopLevel<'bump>],
    pub fun_sigs: &'a [(&'bump str, FunSig)],
    pub enum_types: &'a [(&'bump str, &'bump Term<'bump>)],
    pub struct_types: &'a [(&'bump str, &'bump Term<'bump>)],
}

pub type ExpandedTopLevels<'bump> = Vec<(usize, TopLevel<'bump>)>;
pub type IndexedDiagnostics = Vec<(usize, Diagnostic)>;

#[derive(Clone)]
pub(crate) struct MetaCallable<'bump> {
    pub(crate) name: Name<'bump>,
    pub(crate) params: Vec<Option<&'bump Term<'bump>>>,
}

struct MetaSignatureSpec<'a> {
    marker: &'a str,
    first: &'a str,
    output: &'a str,
    span: std::ops::Range<usize>,
}

/// The compiler orchestrator — owns the bump allocator, term arena, and
/// coordinates parsing, constraint checking, and evaluation.
///
/// Resolution methods are implemented in `resolve.rs` via `impl Compiler`.
pub struct Compiler<'bump> {
    pub(crate) bump: &'bump Bump,
    pub(crate) arena: &'bump TermArena<'bump>,
    pub(crate) checker: TypeChecker<'bump>,
    /// Environment: maps top-level names to their desugared defining terms.
    pub(crate) env: HashMap<&'bump str, &'bump Term<'bump>>,
    /// Accumulated top-level items (for code generation).
    pub tops: Vec<TopLevel<'bump>>,
    /// Raw (un-erased) function definitions for on-demand codegen.
    /// Bodies are resolved & desugared, but type params are NOT erased yet.
    raw_defs: Vec<TopLevel<'bump>>,
    /// Function signatures extracted before erasure (for C codegen).
    fun_sigs: Vec<(&'bump str, FunSig)>,
    /// Enum type definitions collected before erasure (for C codegen).
    pub enum_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    /// Struct type definitions collected before erasure (for C codegen).
    pub struct_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    /// Current-scope implicit parameters introduced by `variable`.
    scoped_implicit_params: Vec<(Name<'bump>, Option<&'bump Term<'bump>>)>,
    /// Data definitions that are safe to reference from erased logical universes.
    pub(crate) termination: HashMap<&'bump str, termination::TerminationInfo>,
    /// Functions registered with `#[tactic]`.
    pub(crate) tactics: HashMap<&'bump str, MetaCallable<'bump>>,
    /// Functions registered with `#[attr]`.
    pub(crate) attributes: HashMap<&'bump str, MetaCallable<'bump>>,
    /// Suppress diagnostic output (set during codegen).
    quiet: bool,
}

impl<'bump> Compiler<'bump> {
    pub fn new(bump: &'bump Bump, arena: &'bump TermArena<'bump>) -> Self {
        let mut compiler = Self {
            bump,
            arena,
            checker: TypeChecker::new(arena),
            env: HashMap::new(),
            tops: vec![],
            raw_defs: vec![],
            fun_sigs: vec![],
            enum_types: vec![],
            struct_types: vec![],
            scoped_implicit_params: Vec::new(),
            termination: HashMap::new(),
            tactics: HashMap::new(),
            attributes: HashMap::new(),
            quiet: false,
        };
        compiler.register_builtin_meta();
        compiler.register_operator_intrinsics();
        compiler
    }

    /// Process a source file: parse it and handle each top-level item.
    pub fn process_file(&mut self, file: &str) -> Result<(), Diagnostic> {
        let content = read_source_file(file)?;
        if modules::is_module_entry(file) || modules::source_uses_modules(&content) {
            return self.process_module_entry(file);
        }
        self.process_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn process_file_str(&mut self, source: &str) -> Result<(), Diagnostic> {
        self.process_str(source, "<str>")
    }

    /// Check recovered top-level items and collect every diagnostic that can be
    /// produced without aborting the whole file. This is intended for editor
    /// integrations that already parsed with a recovery parser.
    pub fn check_top_levels_for_diagnostics(
        &mut self,
        tops: impl IntoIterator<Item = TopLevel<'bump>>,
        file: &str,
        source: &str,
        mode: CheckMode,
    ) -> Vec<Diagnostic> {
        let previous_quiet = self.quiet;
        self.quiet = true;
        let previous_mode = self.checker.mode();
        self.checker.set_mode(mode);
        let mut diagnostics = Vec::new();

        for top in tops {
            if let Err(diagnostic) = self.process_top_level(top) {
                diagnostics.push(diagnostic.with_source_if_missing(file, source));
            }
        }

        self.checker.set_mode(previous_mode);
        self.quiet = previous_quiet;
        diagnostics
    }

    /// Check recovered top-level items while reporting diagnostics only for
    /// selected indices. This lets editor integrations replay unchanged
    /// context to rebuild the compiler environment without invalidating every
    /// cached item diagnostic.
    pub fn check_top_levels_incremental_for_diagnostics(
        &mut self,
        tops: impl IntoIterator<Item = (usize, TopLevel<'bump>, bool)>,
        file: &str,
        source: &str,
        mode: CheckMode,
    ) -> Vec<(usize, Diagnostic)> {
        let previous_quiet = self.quiet;
        self.quiet = true;
        let previous_mode = self.checker.mode();
        self.checker.set_mode(mode);
        let mut diagnostics = Vec::new();

        for (idx, top, report) in tops {
            if let Err(diagnostic) = self.process_top_level(top)
                && report
            {
                diagnostics.push((idx, diagnostic.with_source_if_missing(file, source)));
            }
        }

        self.checker.set_mode(previous_mode);
        self.quiet = previous_quiet;
        diagnostics
    }

    /// Check recovered top-level items and also return the metaprogram-expanded
    /// form of each item that expanded successfully. Editor integrations use
    /// this to build symbol models from the same post-expansion surface that
    /// the checker sees, while still reporting diagnostics against source spans.
    pub fn check_top_levels_with_expansion_for_diagnostics(
        &mut self,
        tops: impl IntoIterator<Item = (usize, TopLevel<'bump>, bool)>,
        file: &str,
        source: &str,
        mode: CheckMode,
    ) -> (ExpandedTopLevels<'bump>, IndexedDiagnostics) {
        let previous_quiet = self.quiet;
        self.quiet = true;
        let previous_mode = self.checker.mode();
        self.checker.set_mode(mode);
        let mut expanded_tops = Vec::new();
        let mut diagnostics = Vec::new();

        for (idx, top, report) in tops {
            match self.expand_meta_tops(top) {
                Ok(expanded) => {
                    if let Some(first) = expanded.first() {
                        expanded_tops.push((idx, first.clone()));
                    }
                    for expanded in expanded {
                        if let Err(diagnostic) = self.process_expanded_top_level(expanded)
                            && report
                        {
                            diagnostics
                                .push((idx, diagnostic.with_source_if_missing(file, source)));
                            break;
                        }
                    }
                }
                Err(diagnostic) if report => {
                    diagnostics.push((idx, diagnostic.with_source_if_missing(file, source)));
                }
                Err(_) => {}
            }
        }

        self.checker.set_mode(previous_mode);
        self.quiet = previous_quiet;
        (expanded_tops, diagnostics)
    }

    fn process_str(&mut self, content: &str, file: &str) -> Result<(), Diagnostic> {
        let tops = parse_program(content, self.bump, self.arena).map_err(|e| {
            Diagnostic::with_span(format!("parse error: {}", e.message), e.span)
                .with_source(file, content)
        })?;
        for top in tops {
            self.process_top_level(top)
                .map_err(|d| d.with_source_if_missing(file, content))?;
        }
        Ok(())
    }

    /// Evaluate an expression string (for `--eval`).
    pub fn eval_expr(&self, expr: &str) -> Result<(), Diagnostic> {
        let term = parse_expr_top(expr, self.bump, self.arena).map_err(|err| {
            Diagnostic::with_span(format!("--eval parse error: {}", err.message), err.span)
                .with_source("--eval", expr)
        })?;
        let resolved = self.try_resolve_all(term)?;
        let self_name = self
            .checker
            .desugar_with_context(term)
            .ok()
            .and_then(|term| self.extract_func_name(term));
        let mut ev = Evaluator::new(self.arena);
        if let Some(n) = self_name {
            ev.set_self_name(n);
        }
        match ev.eval(resolved) {
            Err(err) => Err(Diagnostic::new(format!("--eval error: {}", err))),
            Ok(val) => {
                println!("{}", PrettyPrinter::pretty(val));
                Ok(())
            }
        }
    }

    /// Get the collected top-level items (for code generation).
    pub fn tops(&self) -> &[TopLevel<'bump>] {
        &self.tops
    }

    /// Get un-erased function definitions (for on-demand codegen).
    pub fn raw_defs(&self) -> &[TopLevel<'bump>] {
        &self.raw_defs
    }

    /// Get the function signatures extracted before erasure (for C codegen).
    pub fn fun_sigs(&self) -> &[(&'bump str, FunSig)] {
        &self.fun_sigs
    }

    /// Get a single explicit codegen input view.
    pub fn codegen_input(&self) -> CodegenInput<'_, 'bump> {
        CodegenInput {
            tops: &self.tops,
            raw_defs: &self.raw_defs,
            fun_sigs: &self.fun_sigs,
            enum_types: &self.enum_types,
            struct_types: &self.struct_types,
        }
    }

    // ── private helpers ──

    /// Desugar a generic enum/struct definition (one with type parameters)
    /// into `Annot(Lam(...), Pi(...))` for env storage.
    fn desugar_top_def(
        &self,
        _name: Name<'bump>,
        params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
        let desugarer = crate::core::debruijn::Desugarer::new(self.arena);
        let func_body = params.iter().rfold(
            desugarer.desugar_with_names(body, &names),
            |b, &(_pn, _)| self.arena.lam(b),
        );
        let default = self.arena.builtin(self.arena.alloc_str("data"));
        let ret = m_ret
            .map(|t| desugarer.desugar_with_names(t, &names))
            .unwrap_or(default);
        let func_constraint = params
            .iter()
            .enumerate()
            .rev()
            .fold(ret, |b, (idx, &(pn, mc))| {
                let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
                let dom = mc
                    .map(|t| desugarer.desugar_with_names(t, &dom_env))
                    .unwrap_or(default);
                self.arena.pi(pn, dom, b)
            });
        self.arena.annot(func_body, func_constraint)
    }

    fn desugar_checked_def(
        &self,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
        if matches!(body, Term::EnumDef(..) | Term::StructDef(..)) {
            return self.checker.desugar_with_names_context(body, &names);
        }
        let mut method_scope = params
            .iter()
            .map(
                |(name, constraint)| crate::compiler::resolve::MethodScopeEntry {
                    name,
                    constraint: *constraint,
                },
            )
            .collect::<Vec<_>>();
        let body = self.rewrite_method_calls(body, &mut method_scope)?;
        let default = self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA));
        let ret = m_ret
            .map(|t| self.checker.desugar_with_names_context(t, &names))
            .transpose()?
            .unwrap_or(default);
        let raw_body = if Self::contains_do(body) {
            let resolver = |name: &str| self.checker.lookup_variant(name);
            crate::core::debruijn::Desugarer::new(self.arena)
                .try_desugar_with_names_variant_resolver_and_effect(body, &names, &resolver, ret)
                .map_err(Diagnostic::new)?
        } else {
            self.checker.desugar_with_names_context(body, &names)?
        };
        let func_body = params
            .iter()
            .rfold(raw_body, |b, &(_pn, _)| self.arena.lam(b));
        let func_constraint =
            params
                .iter()
                .enumerate()
                .rev()
                .try_fold(ret, |b, (idx, &(pn, mc))| {
                    let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
                    let dom = mc
                        .map(|t| self.checker.desugar_with_names_context(t, &dom_env))
                        .transpose()?
                        .unwrap_or(default);
                    Ok::<_, Diagnostic>(self.arena.pi(pn, dom, b))
                })?;
        Ok(self.arena.annot(func_body, func_constraint))
    }

    /// Process a single top-level item.
    fn process_top_level(&mut self, top: TopLevel<'bump>) -> Result<(), Diagnostic> {
        for top in self.expand_meta_tops(top)? {
            self.process_expanded_top_level(top)?;
        }
        Ok(())
    }

    fn process_expanded_top_level(&mut self, top: TopLevel<'bump>) -> Result<(), Diagnostic> {
        match top {
            TopLevel::TLDef(name, params, m_ret, body, span) => {
                let params = self.with_scoped_implicit_params(params);
                self.process_def(name, params, m_ret, body, span, TerminationClaim::None)?;
            }
            TopLevel::TLExternDef(name, params, ret, span) => {
                self.process_extern_def(name, params, ret, span)?;
            }
            TopLevel::TLInstance(name, constraint, value, span) => {
                self.process_instance(name, constraint, value, span)?;
            }
            TopLevel::TLVariable(params, _) => {
                self.scoped_implicit_params.extend(params.iter().copied());
            }
            TopLevel::TLCheck(term, constraint, span) => {
                self.process_check(term, constraint, span)?;
            }
            TopLevel::TLTheorem(name, prop, body, span) => {
                self.process_theorem(name, prop, body, span)?;
            }
            TopLevel::TLPublic(inner) => {
                self.process_expanded_top_level((*inner).clone())?;
            }
            TopLevel::TLAttributed(attrs, inner, span) => {
                if attrs.iter().any(|attr| {
                    attr.is_name(COMPILER_INTRINSIC_ATTR)
                        || attr.is_name(COMPILER_BUILTIN_ATTRIBUTE_ATTR)
                }) {
                    return Ok(());
                }
                let claim = self.termination_claim_from_attrs(attrs, span)?;
                if claim.is_user_claim()
                    && self.process_terminating_attributed_top((*inner).clone(), claim)?
                {
                    return Ok(());
                }
                if self.process_meta_callable_attributed_top(attrs, (*inner).clone())? {
                    return Ok(());
                }
                self.process_expanded_top_level((*inner).clone())?;
            }
            TopLevel::TLUse(..) => {}
            TopLevel::TLMod(..) => {}
            TopLevel::TLNamespace(name, items, _) => {
                let scope_len = self.scoped_implicit_params.len();
                for item in items {
                    self.process_namespace_top(name, item.clone())?;
                }
                self.scoped_implicit_params.truncate(scope_len);
            }
            TopLevel::TLEval(term, span) => {
                self.process_eval_like(term, span, "eval")?;
            }
            TopLevel::TLExpr(term, span) => {
                self.process_eval_like(term, span, "eval")?;
            }
            TopLevel::TLSplice(..) => unreachable!("top-level splice should be expanded first"),
        }
        Ok(())
    }

    fn process_namespace_top(
        &mut self,
        namespace: Name<'bump>,
        top: TopLevel<'bump>,
    ) -> Result<(), Diagnostic> {
        self.process_namespace_top_with_termination(namespace, top, TerminationClaim::None)
    }

    fn process_terminating_attributed_top(
        &mut self,
        top: TopLevel<'bump>,
        claim: TerminationClaim<'bump>,
    ) -> Result<bool, Diagnostic> {
        match top {
            TopLevel::TLPublic(inner) => {
                self.process_terminating_attributed_top((*inner).clone(), claim)
            }
            TopLevel::TLDef(name, params, m_ret, body, span) => {
                let params = self.with_scoped_implicit_params(params);
                self.process_def(name, params, m_ret, body, span, claim)?;
                Ok(true)
            }
            TopLevel::TLNamespace(namespace, items, _) => {
                let scope_len = self.scoped_implicit_params.len();
                for item in items {
                    self.process_namespace_top_with_termination(namespace, item.clone(), claim)?;
                }
                self.scoped_implicit_params.truncate(scope_len);
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn process_namespace_top_with_termination(
        &mut self,
        namespace: Name<'bump>,
        top: TopLevel<'bump>,
        termination_claim: TerminationClaim<'bump>,
    ) -> Result<(), Diagnostic> {
        let qualify = |name: Name<'bump>| self.arena.alloc_str(&format!("{namespace}::{name}"));
        match top {
            TopLevel::TLPublic(inner) => self.process_namespace_top_with_termination(
                namespace,
                (*inner).clone(),
                termination_claim,
            ),
            TopLevel::TLAttributed(attrs, inner, span) => {
                if attrs.iter().any(|attr| {
                    attr.is_name(COMPILER_INTRINSIC_ATTR)
                        || attr.is_name(COMPILER_BUILTIN_ATTRIBUTE_ATTR)
                }) {
                    return Ok(());
                }
                let termination_claim =
                    termination_claim.merge(self.termination_claim_from_attrs(attrs, span)?);
                if self.process_namespace_meta_callable_attributed_top(
                    namespace,
                    attrs,
                    (*inner).clone(),
                    termination_claim,
                )? {
                    return Ok(());
                }
                self.process_namespace_top_with_termination(
                    namespace,
                    (*inner).clone(),
                    termination_claim,
                )
            }
            TopLevel::TLDef(name, params, ret, body, span) => {
                let params = self.with_scoped_implicit_params(params);
                self.process_def(qualify(name), params, ret, body, span, termination_claim)
            }
            TopLevel::TLExternDef(name, params, ret, span) => {
                self.process_extern_def(qualify(name), params, ret, span)
            }
            TopLevel::TLInstance(name, constraint, value, span) => {
                self.process_instance(qualify(name), constraint, value, span)
            }
            TopLevel::TLVariable(params, _) => {
                self.scoped_implicit_params.extend(params.iter().copied());
                Ok(())
            }
            TopLevel::TLTheorem(name, prop, body, span) => {
                self.process_theorem(qualify(name), prop, body, span)
            }
            _ => Ok(()),
        }
    }

    fn with_scoped_implicit_params(
        &self,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
    ) -> &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)] {
        if self.scoped_implicit_params.is_empty() {
            return params;
        }
        let mut all = Vec::with_capacity(self.scoped_implicit_params.len() + params.len());
        all.extend(self.scoped_implicit_params.iter().copied());
        all.extend(params.iter().copied());
        self.arena.alloc_slice(&all)
    }

    fn process_meta_callable_attributed_top(
        &mut self,
        attrs: &'bump [crate::front::parser::Attribute<'bump>],
        top: TopLevel<'bump>,
    ) -> Result<bool, Diagnostic> {
        let has_tactic = attrs.iter().any(|attr| attr.is_name(TACTIC_ATTR));
        let has_attr = attrs.iter().any(|attr| attr.is_name(CUSTOM_ATTRIBUTE_ATTR));
        if !has_tactic && !has_attr {
            return Ok(false);
        }
        match top {
            TopLevel::TLPublic(inner) => {
                self.process_meta_callable_attributed_top(attrs, (*inner).clone())
            }
            TopLevel::TLDef(name, params, m_ret, body, span) => {
                let params = self.with_scoped_implicit_params(params);
                self.validate_and_register_meta_markers(
                    name,
                    params,
                    m_ret,
                    has_tactic,
                    has_attr,
                    span.clone(),
                )?;
                self.process_def(name, params, m_ret, body, span, TerminationClaim::None)?;
                Ok(true)
            }
            _ => Err(Diagnostic::new(
                "#[tactic] and #[attr] may only prefix `def`",
            )),
        }
    }

    fn process_namespace_meta_callable_attributed_top(
        &mut self,
        namespace: Name<'bump>,
        attrs: &'bump [crate::front::parser::Attribute<'bump>],
        top: TopLevel<'bump>,
        termination_claim: TerminationClaim<'bump>,
    ) -> Result<bool, Diagnostic> {
        let has_tactic = attrs.iter().any(|attr| attr.is_name(TACTIC_ATTR));
        let has_attr = attrs.iter().any(|attr| attr.is_name(CUSTOM_ATTRIBUTE_ATTR));
        if !has_tactic && !has_attr {
            return Ok(false);
        }
        let qualify = |name: Name<'bump>| self.arena.alloc_str(&format!("{namespace}::{name}"));
        match top {
            TopLevel::TLPublic(inner) => self.process_namespace_meta_callable_attributed_top(
                namespace,
                attrs,
                (*inner).clone(),
                termination_claim,
            ),
            TopLevel::TLDef(name, params, m_ret, body, span) => {
                let qname = qualify(name);
                let params = self.with_scoped_implicit_params(params);
                self.validate_and_register_meta_markers(
                    qname,
                    params,
                    m_ret,
                    has_tactic,
                    has_attr,
                    span.clone(),
                )?;
                self.process_def(qname, params, m_ret, body, span, termination_claim)?;
                Ok(true)
            }
            _ => Err(Diagnostic::new(
                "#[tactic] and #[attr] may only prefix `def`",
            )),
        }
    }

    fn validate_and_register_meta_markers(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        ret: Option<&'bump Term<'bump>>,
        has_tactic: bool,
        has_attr: bool,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        if has_tactic {
            self.validate_meta_callable_signature(
                name,
                params,
                ret,
                MetaSignatureSpec {
                    marker: TACTIC_ATTR,
                    first: crate::compiler::meta::EXPR_TYPE,
                    output: crate::compiler::meta::EXPR_TYPE,
                    span: span.clone(),
                },
            )?;
            self.tactics.insert(
                name,
                MetaCallable {
                    name,
                    params: params.iter().map(|(_, c)| *c).collect(),
                },
            );
        }
        if has_attr {
            self.validate_meta_callable_signature(
                name,
                params,
                ret,
                MetaSignatureSpec {
                    marker: CUSTOM_ATTRIBUTE_ATTR,
                    first: crate::compiler::meta::EXPR_TYPE,
                    output: crate::compiler::meta::DEFINITIONS_TYPE,
                    span,
                },
            )?;
            self.attributes.insert(
                name,
                MetaCallable {
                    name,
                    params: params.iter().map(|(_, c)| *c).collect(),
                },
            );
        }
        Ok(())
    }

    fn validate_meta_callable_signature(
        &self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        ret: Option<&'bump Term<'bump>>,
        spec: MetaSignatureSpec<'_>,
    ) -> Result<(), Diagnostic> {
        let first_param = params.first().and_then(|(_, c)| *c);
        if !first_param.is_some_and(|ty| Self::is_meta_type_name(ty, spec.first)) {
            return Err(Diagnostic::with_span(
                format!(
                    "function `{name}` cannot be used as {}: first parameter must be {}",
                    spec.marker, spec.first
                ),
                spec.span,
            ));
        }
        if !ret.is_some_and(|ty| Self::is_meta_type_name(ty, spec.output)) {
            return Err(Diagnostic::with_span(
                format!(
                    "function `{name}` cannot be used as {}: return value must be {}",
                    spec.marker, spec.output
                ),
                spec.span,
            ));
        }
        Ok(())
    }

    pub(crate) fn is_meta_type_name(term: &Term<'_>, expected: &str) -> bool {
        match term {
            Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
                crate::config::canonical_builtin_name(name) == expected
            }
            Term::Annot(inner, _) | Term::Implicit(inner) => {
                Self::is_meta_type_name(inner, expected)
            }
            _ => false,
        }
    }

    fn process_def(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
        termination_claim: TerminationClaim<'bump>,
    ) -> Result<(), Diagnostic> {
        let name = self.codegen_attribute_target_name(name);
        let body = self.desugar_checked_def(params, m_ret, body)?;
        let semantics = SemanticQueries::new(self.checker.builtins());
        let universe = semantics.universe(&empty_ctx(), body);
        if self.definition_result_is_erased_universe(body)? {
            self.ensure_logic_data_refs_terminate(body, span.clone())?;
        }
        if universe == Some(Universe::UProp) {
            self.ensure_logic_data_refs_terminate(body, span.clone())?;
            self.validate_runtime_members_are_data(body)
                .map_err(|err| {
                    Self::wrap_diagnostic(format!("definition {name} failed"), err, span.clone())
                })?;
            if self.register_prop_definition(name, params, m_ret, body) {
                return Ok(());
            }
        }

        let has_erased_parameter = self.has_erased_parameter(params);
        let previous = if has_erased_parameter {
            self.env.insert(name, body)
        } else {
            self.env.insert(name, self.definition_signature(body))
        };
        let resolved_body = if has_erased_parameter {
            None
        } else {
            Some(self.try_resolve_all(body)?)
        };
        if let Some(resolved_body) = resolved_body
            && let Err(err) = self.checker.check(
                &empty_ctx(),
                resolved_body,
                self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
            )
        {
            self.restore_env_binding(name, previous);
            return Err(Self::wrap_diagnostic(
                format!("definition {name} failed"),
                err,
                span,
            ));
        }

        if !self.quiet {
            println!("[defined] {}", name);
        }
        self.verify_termination_claim(termination_claim, span.clone())?;
        self.record_data_termination(name, body, termination_claim);
        let stored_body = if body.is_constant() {
            resolved_body.unwrap_or_else(|| self.subst_top_level(body))
        } else {
            body
        };
        self.env.insert(name, stored_body);
        Ok(())
    }

    fn process_extern_def(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        ret: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        for (pname, constraint) in params {
            if constraint.is_none() {
                return Err(Diagnostic::with_span(
                    format!("extern parameter `{pname}` requires an explicit constraint"),
                    span,
                ));
            }
        }
        let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
        let ret = self.checker.desugar_with_names_context(ret, &names)?;
        let signature =
            params
                .iter()
                .enumerate()
                .rev()
                .try_fold(ret, |cod, (idx, &(pn, mc))| {
                    let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
                    let dom = self
                        .checker
                        .desugar_with_names_context(mc.expect("checked above"), &dom_env)?;
                    Ok::<_, Diagnostic>(self.arena.pi(pn, dom, cod))
                })?;
        let symbol = self.arena.global(name);
        let typed_symbol = self.arena.annot(symbol, signature);
        self.checker.add_extern(name, signature);
        self.mark_extern_terminating(name);
        self.env.insert(name, typed_symbol);
        if !self.quiet {
            println!("[extern] {}", name);
        }
        Ok(())
    }

    fn process_instance(
        &mut self,
        name: Name<'bump>,
        constraint: &'bump Term<'bump>,
        value: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        let resolved_constraint = self.checker.desugar_with_context(constraint)?;
        let resolved_value = self.resolve_instance_value(value, resolved_constraint)?;
        let resolved_value = self.attach_global_signatures(resolved_value);
        self.checker
            .check(&empty_ctx(), resolved_value, resolved_constraint)
            .map_err(|err| {
                Self::wrap_diagnostic(format!("instance {name} failed"), err, span.clone())
            })?;
        self.checker
            .add_instance(name, resolved_constraint, resolved_value);
        if !self.quiet {
            println!("[instance] {}", name);
        }
        Ok(())
    }

    fn restore_env_binding(&mut self, name: Name<'bump>, previous: Option<&'bump Term<'bump>>) {
        if let Some(prev) = previous {
            self.env.insert(name, prev);
        } else {
            self.env.remove(name);
        }
    }

    fn attach_global_signatures(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(term, &|node| {
            if let Term::Builtin(name) | Term::Global(name) = node
                && let Some(Term::Annot(_, signature)) = self.env.get(name).copied()
            {
                return Some(self.arena.annot(self.arena.global(name), signature));
            }
            None
        })
    }

    fn process_check(
        &self,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        let resolved_constraint = self.try_resolve_all(constraint)?;
        let resolved = self.try_resolve_all_with_expected(term, Some(resolved_constraint))?;
        if self.is_erased_universe_constraint(constraint)? {
            let logical_term = self.checker.desugar_with_context(term)?;
            self.ensure_logic_data_refs_terminate(logical_term, span.clone())?;
        }
        match self
            .checker
            .check(&empty_ctx(), resolved, resolved_constraint)
        {
            Err(err) => Err(Self::wrap_diagnostic("check failed", err, span)),
            Ok(_) => {
                if !self.quiet {
                    println!("[OK]");
                }
                Ok(())
            }
        }
    }

    fn process_theorem(
        &mut self,
        name: Name<'bump>,
        prop: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
    ) -> Result<(), Diagnostic> {
        let logical_prop = self.checker.desugar_with_context(prop)?;
        let logical_body = self.checker.desugar_with_context(body)?;
        self.ensure_logic_data_refs_terminate(logical_prop, span.clone())?;
        self.ensure_logic_data_refs_terminate(logical_body, span.clone())?;
        let resolved_prop = self.try_resolve_all(prop)?;
        let resolved_body = self.try_resolve_all_with_expected(body, Some(resolved_prop))?;
        match self
            .checker
            .check(&empty_ctx(), resolved_body, resolved_prop)
        {
            Err(err) => Err(Self::wrap_diagnostic("theorem check failed", err, span)),
            Ok(_) => {
                if !self.quiet {
                    println!("[theorem] {}", name);
                }
                self.env
                    .insert(name, self.arena.annot(resolved_body, resolved_prop));
                Ok(())
            }
        }
    }

    fn process_eval_like(
        &self,
        term: &'bump Term<'bump>,
        span: std::ops::Range<usize>,
        label: &str,
    ) -> Result<(), Diagnostic> {
        let resolved = self.try_resolve_all(term)?;
        self.checker
            .check(
                &empty_ctx(),
                resolved,
                self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
            )
            .map_err(|err| {
                Self::wrap_diagnostic(format!("{label} check failed"), err, span.clone())
            })?;
        if self.quiet {
            return Ok(());
        }
        let self_name = self
            .checker
            .desugar_with_context(term)
            .ok()
            .and_then(|term| self.extract_func_name(term));
        let mut ev = Evaluator::new(self.arena);
        if let Some(n) = self_name {
            ev.set_self_name(n);
        }
        match ev.eval(resolved) {
            Err(err) => Err(Diagnostic::with_span(
                format!("{label} error: {}", err),
                span,
            )),
            Ok(val) => {
                println!("{}", PrettyPrinter::pretty(val));
                Ok(())
            }
        }
    }

    fn register_prop_definition(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> bool {
        match body {
            Term::EnumDef(..) => {
                if !self.quiet {
                    println!("[enum] {}", name);
                }
                let type_param_names: Vec<_> = params.iter().map(|(n, _)| *n).collect();
                let type_params = self.arena.alloc_slice(&type_param_names);
                self.checker.add_enum(name, body, type_params);
                if !params.is_empty() {
                    let term = self.desugar_top_def(name, params, m_ret, body);
                    self.env.insert(name, term);
                }
                true
            }
            Term::StructDef(..) => {
                if !self.quiet {
                    println!("[struct] {}", name);
                }
                let type_param_names: Vec<_> = params.iter().map(|(n, _)| *n).collect();
                let type_params = self.arena.alloc_slice(&type_param_names);
                self.checker.add_struct(name, body, type_params);
                if !params.is_empty() {
                    let term = self.desugar_top_def(name, params, m_ret, body);
                    self.env.insert(name, term);
                }
                true
            }
            _ if params.is_empty() => {
                let Some(desugared) = self.checker.desugar_with_context(body).ok() else {
                    return false;
                };
                if let Some((parent, predicate)) = Self::refinement_parts(desugared) {
                    if !self.quiet {
                        println!("[refinement] {}", name);
                    }
                    self.checker.add_refinement(name, parent, predicate);
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn register_operator_intrinsics(&mut self) {
        self.register_intrinsic_binop("std::primitive::int_add", PrimOp::Add, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_sub", PrimOp::Sub, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_mul", PrimOp::Mul, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_div", PrimOp::Div, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_mod", PrimOp::Mod_, "int", "int", "int");
        self.register_intrinsic_binop("std::primitive::int_eq", PrimOp::Eq, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_lt", PrimOp::Lt, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_gt", PrimOp::Gt, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_le", PrimOp::Le, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_ge", PrimOp::Ge, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::int_neq", PrimOp::Neq, "int", "int", "bool");
        self.register_intrinsic_binop("std::primitive::str_add", PrimOp::Add, "str", "str", "str");
    }

    fn register_intrinsic_binop(
        &mut self,
        name: &'static str,
        op: PrimOp,
        left: &str,
        right: &str,
        ret: &str,
    ) {
        let left = self.arena.builtin(self.arena.alloc_str(left));
        let right = self.arena.builtin(self.arena.alloc_str(right));
        let ret = self.arena.builtin(self.arena.alloc_str(ret));
        let sig = self.arena.pi(
            self.arena.alloc_str(""),
            left,
            self.arena.pi(self.arena.alloc_str(""), right, ret),
        );
        self.env.insert(
            self.arena.alloc_str(name),
            self.arena.annot(self.arena.prim_op(op), sig),
        );
    }

    fn validate_runtime_members_are_data(
        &self,
        body: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        match body {
            Term::EnumDef(enum_name, variants) => {
                for (variant_name, fields) in variants.iter() {
                    for (field_name, constraint) in fields.iter() {
                        if Self::is_direct_prop_runtime_member(constraint) {
                            return Err(Diagnostic::new(format!(
                                "data enum {} variant {} field '{}' cannot use prop/theorem/proof as a runtime member",
                                enum_name, variant_name, field_name
                            )));
                        }
                    }
                }
            }
            Term::StructDef(struct_name, fields) => {
                for (field_name, constraint) in fields.iter() {
                    if Self::is_direct_prop_runtime_member(constraint) {
                        return Err(Diagnostic::new(format!(
                            "data struct {} field '{}' cannot use prop/theorem/proof as a runtime member",
                            struct_name, field_name
                        )));
                    }
                }
            }
            Term::Annot(inner, _) => self.validate_runtime_members_are_data(inner)?,
            _ => {}
        }
        Ok(())
    }

    fn is_direct_prop_runtime_member(term: &Term<'_>) -> bool {
        match term {
            Term::Builtin(name) | Term::Global(name) | Term::Named(name) => matches!(
                canonical_builtin_name(name),
                BUILTIN_PROP | BUILTIN_THEOREM | BUILTIN_PROOF
            ),
            Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
            Term::Implicit(inner) | Term::Annot(inner, _) => {
                Self::is_direct_prop_runtime_member(inner)
            }
            _ => false,
        }
    }

    fn has_erased_parameter(&self, params: &[(Name<'bump>, Option<&'bump Term<'bump>>)]) -> bool {
        let semantics = SemanticQueries::new(self.checker.builtins());
        params.iter().any(|(_, c)| {
            c.is_some_and(|constraint| semantics.is_erased_parameter_constraint(constraint))
        })
    }

    fn definition_signature(&self, body: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match body {
            Term::Annot(_, constraint) => {
                let stub = self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA));
                self.arena.annot(stub, constraint)
            }
            _ => body,
        }
    }

    fn refinement_parts(
        body: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
        match body {
            Term::Refine(_, parent, predicate) => Some((*parent, *predicate)),
            Term::Annot(inner, _) => Self::refinement_parts(inner),
            _ => None,
        }
    }

    fn contains_do(term: &Term<'_>) -> bool {
        match term {
            Term::Do(_) => true,
            Term::Unsafe(inner) | Term::Pure(inner) => Self::contains_do(inner),
            Term::App(f, a) => Self::contains_do(f) || Self::contains_do(a),
            Term::NamedLam(_, body) | Term::Lam(body) => Self::contains_do(body),
            Term::Pi(_, a, b) => Self::contains_do(a) || Self::contains_do(b),
            Term::Let(_, val, body, mc) => {
                Self::contains_do(val)
                    || Self::contains_do(body)
                    || mc.is_some_and(Self::contains_do)
            }
            Term::IfThenElse(c, t, f) => {
                Self::contains_do(c) || Self::contains_do(t) || Self::contains_do(f)
            }
            Term::Refine(_, parent, pred) => Self::contains_do(parent) || Self::contains_do(pred),
            Term::Annot(inner, constraint) => {
                Self::contains_do(inner) || Self::contains_do(constraint)
            }
            Term::ByProof(inner, tactics) => {
                inner.is_some_and(Self::contains_do)
                    || tactics.iter().any(|t| match t {
                        crate::core::syntax::Tactic::Exact(t)
                        | crate::core::syntax::Tactic::Apply(t)
                        | crate::core::syntax::Tactic::Have(_, t) => Self::contains_do(t),
                        crate::core::syntax::Tactic::Intro(_) => false,
                        crate::core::syntax::Tactic::Custom(_, args) => {
                            args.iter().any(|arg| Self::contains_do(arg))
                        }
                    })
            }
            Term::EnumDef(_, variants) => variants.iter().any(|(_, fields)| {
                fields
                    .iter()
                    .any(|(_, constraint)| Self::contains_do(constraint))
            }),
            Term::Variant(_, _, payloads) | Term::StructCons(_, payloads) => {
                payloads.iter().any(|t| Self::contains_do(t))
            }
            Term::Match(scrut, branches) => {
                Self::contains_do(scrut)
                    || branches.iter().any(|(_, binds, body)| {
                        Self::contains_do(body)
                            || binds
                                .iter()
                                .any(|(_, constraint)| Self::contains_do(constraint))
                    })
            }
            Term::NamedMatch(scrut, branches) => {
                Self::contains_do(scrut)
                    || branches.iter().any(|(_, binds, body)| {
                        Self::contains_do(body)
                            || binds
                                .iter()
                                .any(|(_, constraint)| Self::contains_do(constraint))
                    })
            }
            Term::StructDef(_, fields) => fields.iter().any(|(_, c)| Self::contains_do(c)),
            Term::StructProj(subject, _) => Self::contains_do(subject),
            Term::MethodCall(subject, _) => Self::contains_do(subject),
            _ => false,
        }
    }

    pub(crate) fn codegen_attribute_target_name(&self, name: Name<'bump>) -> Name<'bump> {
        name.strip_prefix(GLOBAL_ALLOCATOR_NAME_PREFIX)
            .map(|stripped| self.arena.alloc_str(stripped))
            .unwrap_or(name)
    }

    fn is_erased_universe_constraint(&self, term: &'bump Term<'bump>) -> Result<bool, Diagnostic> {
        let term = self.checker.desugar_with_context(term)?;
        Ok(match term {
            Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
            Term::Builtin(name) | Term::Global(name) => matches!(
                crate::config::canonical_builtin_name(name),
                crate::config::BUILTIN_PROP
                    | crate::config::BUILTIN_THEOREM
                    | crate::config::BUILTIN_PROOF
            ),
            _ => false,
        })
    }

    fn definition_result_is_erased_universe(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<bool, Diagnostic> {
        let Some(result) = Self::definition_result_constraint(term) else {
            return Ok(false);
        };
        self.is_erased_universe_constraint(result)
    }

    fn definition_result_constraint(term: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        let Term::Annot(_, constraint) = term else {
            return None;
        };
        let mut result = *constraint;
        while let Term::Pi(_, _, codomain) = result {
            result = codomain;
        }
        Some(result)
    }

    fn wrap_diagnostic(
        prefix: impl Into<String>,
        mut err: Diagnostic,
        fallback_span: std::ops::Range<usize>,
    ) -> Diagnostic {
        err.message = format!("{}: {}", prefix.into(), err.message);
        if err.span.is_none() {
            err.span = Some(fallback_span);
        }
        err
    }
}
