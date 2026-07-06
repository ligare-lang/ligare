//! Compiler orchestrator — coordinates parsing, constraint checking, and code generation.
//!
//! Resolution logic lives in `resolve.rs`; this module holds the `Compiler`
//! struct and its lifecycle methods.

pub mod cache;
mod meta;
pub mod modules;
mod pipeline;
mod processing;
mod resolve;
mod termination;

use std::collections::HashMap;
use std::fs;

use bumpalo::Bump;
use ligare_backend::CodegenInput;

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

    /// Get a single explicit codegen input view.
    pub fn codegen_input(&self) -> CodegenInput<'_, 'bump> {
        CodegenInput {
            tops: &self.tops,
            raw_defs: &self.raw_defs,
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
}
