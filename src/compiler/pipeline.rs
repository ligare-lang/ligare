use crate::checker::context::lookup_refine;
use crate::checker::context::empty_ctx;
use crate::checker::erase::Eraser;
use crate::config::COMPILER_INTRINSIC_ATTR;
use crate::core::semantics::SemanticQueries;
use crate::core::syntax::Term;
use crate::diagnostic::Diagnostic;
use crate::front::parser::{TopLevel, parse_program};

use super::{Compiler, read_source_file};

struct ParsedProgram<'bump> {
    tops: Vec<TopLevel<'bump>>,
}

pub(crate) struct CodegenState<'bump> {
    pub(crate) raw_defs: Vec<TopLevel<'bump>>,
    pub(crate) fun_sigs: Vec<(&'bump str, crate::backend::ir::FunSig)>,
    pub(crate) enum_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    pub(crate) struct_types: Vec<(&'bump str, &'bump Term<'bump>)>,
}

impl<'bump> CodegenState<'bump> {
    pub(crate) fn empty() -> Self {
        Self {
            raw_defs: Vec::new(),
            fun_sigs: Vec::new(),
            enum_types: Vec::new(),
            struct_types: Vec::new(),
        }
    }
}

pub(crate) struct MonomorphizedProgram<'bump> {
    pub(crate) tops: Vec<TopLevel<'bump>>,
    pub(crate) codegen: CodegenState<'bump>,
}

pub(crate) struct ErasedProgram<'bump> {
    pub(crate) tops: Vec<TopLevel<'bump>>,
}

impl<'bump> Compiler<'bump> {
    /// Process a source file, collect top-level items, and check constraints.
    pub fn collect_file(&mut self, file: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        let content = read_source_file(file)?;
        if super::modules::is_module_entry(file) || super::modules::source_uses_modules(&content) {
            return self.collect_module_entry(file);
        }
        self.collect_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn collect_file_str(&mut self, source: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        self.collect_str(source, "<str>")
    }

    fn collect_str(&mut self, content: &str, file: &str) -> Result<(), Diagnostic> {
        let parsed = self.parse_program_for_collection(content, file)?;
        let mut tops = Vec::new();
        for top in parsed.tops {
            let expanded = self
                .expand_meta_tops(top)
                .map_err(|d| d.with_source_if_missing(file, content))?;
            for top in expanded {
                self.process_expanded_top_level(top.clone())
                    .map_err(|d| d.with_source_if_missing(file, content))?;
                tops.push(top);
            }
        }
        let codegen_tops = self.expand_scoped_variable_params(&tops);
        let codegen = self.collect_codegen_state(&codegen_tops)?;
        let monomorphized = self.monomorphize_for_codegen(codegen_tops, codegen)?;
        let current_raw_defs = monomorphized.codegen.raw_defs.clone();
        self.apply_codegen_state(monomorphized.codegen);

        let eraser = Eraser::new(self.arena, self.checker.builtins.clone());
        let erased = self.erase_and_collect_tops(monomorphized.tops, &current_raw_defs, &eraser)?;
        self.tops.extend(erased.tops);
        Ok(())
    }

    fn parse_program_for_collection(
        &self,
        content: &str,
        file: &str,
    ) -> Result<ParsedProgram<'bump>, Diagnostic> {
        let tops = parse_program(content, self.bump, self.arena).map_err(|e| {
            Diagnostic::with_span(format!("parse error: {}", e.message), e.span)
                .with_source(file, content)
        })?;
        Ok(ParsedProgram { tops })
    }

    fn expand_scoped_variable_params(&self, tops: &[TopLevel<'bump>]) -> Vec<TopLevel<'bump>> {
        let mut scoped = Vec::new();
        self.expand_scoped_variable_params_in(tops, &mut scoped)
    }

    fn expand_scoped_variable_params_in(
        &self,
        tops: &[TopLevel<'bump>],
        scoped: &mut Vec<(&'bump str, Option<&'bump Term<'bump>>)>,
    ) -> Vec<TopLevel<'bump>> {
        let mut out = Vec::with_capacity(tops.len());
        for top in tops {
            match top {
                TopLevel::TLVariable(params, _) => {
                    scoped.extend(params.iter().copied());
                }
                TopLevel::TLDef(name, params, ret, body, span) => {
                    let params = if scoped.is_empty() {
                        *params
                    } else {
                        let mut all = Vec::with_capacity(scoped.len() + params.len());
                        all.extend(scoped.iter().copied());
                        all.extend(params.iter().copied());
                        self.arena.alloc_slice(&all)
                    };
                    out.push(TopLevel::TLDef(name, params, *ret, body, span.clone()));
                }
                TopLevel::TLNamespace(name, items, span) => {
                    let scope_len = scoped.len();
                    let items = self.expand_scoped_variable_params_in(items, scoped);
                    scoped.truncate(scope_len);
                    out.push(TopLevel::TLNamespace(
                        name,
                        self.arena.bump().alloc_slice_clone(&items),
                        span.clone(),
                    ));
                }
                TopLevel::TLPublic(inner) => {
                    let expanded =
                        self.expand_scoped_variable_params_in(&[(*inner).clone()], scoped);
                    if let Some(expanded) = expanded.into_iter().next() {
                        out.push(TopLevel::TLPublic(self.arena.bump().alloc(expanded)));
                    }
                }
                TopLevel::TLAttributed(attrs, inner, span) => {
                    let expanded =
                        self.expand_scoped_variable_params_in(&[(*inner).clone()], scoped);
                    if let Some(expanded) = expanded.into_iter().next() {
                        out.push(TopLevel::TLAttributed(
                            attrs,
                            self.arena.bump().alloc(expanded),
                            span.clone(),
                        ));
                    }
                }
                other => out.push(other.clone()),
            }
        }
        out
    }

    /// Collect the codegen-facing inputs from the original un-erased tops.
    pub(crate) fn collect_codegen_state(
        &self,
        tops: &[TopLevel<'bump>],
    ) -> Result<CodegenState<'bump>, Diagnostic> {
        let mut state = CodegenState::empty();
        if let Some((expr_def, _)) = self.checker.lookup_enum(crate::compiler::meta::EXPR_TYPE) {
            state.enum_types.push((
                self.arena.alloc_str(crate::compiler::meta::EXPR_TYPE),
                expr_def,
            ));
        }
        if let Some((definitions_def, _)) = self
            .checker
            .lookup_enum(crate::compiler::meta::DEFINITIONS_TYPE)
        {
            state.enum_types.push((
                self.arena
                    .alloc_str(crate::compiler::meta::DEFINITIONS_TYPE),
                definitions_def,
            ));
        }
        for top in tops {
            let logical_top = Self::logical_codegen_top(top);
            if let TopLevel::TLDef(name, params, _m_ret, body, _) = logical_top {
                let name = self.codegen_attribute_target_name(name);
                let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
                if matches!(body, Term::EnumDef(..)) {
                    let body = self.checker.desugar_with_names_context(body, &names)?;
                    let body = self.normalize_codegen_type_def(body);
                    state.enum_types.push((name, body));
                } else if matches!(body, Term::StructDef(..)) {
                    let body = self.checker.desugar_with_names_context(body, &names)?;
                    let body = self.normalize_codegen_type_def(body);
                    if !Self::is_erased_interface_struct(body) {
                        state.struct_types.push((name, body));
                    }
                }
            }
        }

        for top in tops {
            let logical_top = Self::logical_codegen_top(top);
            if let TopLevel::TLExternDef(name, params, ret, span) = logical_top {
                let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
                let core_params = params
                    .iter()
                    .enumerate()
                    .map(|(idx, (pn, mc))| {
                        let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
                        Ok((
                            *pn,
                            mc.map(|t| self.checker.desugar_with_names_context(t, &dom_env))
                                .map(|r| r.map(|t| self.normalize_codegen_constraint(t)))
                                .transpose()?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                let core_ret = self
                    .checker
                    .desugar_with_names_context(ret, &names)
                    .map(|t| self.normalize_codegen_constraint(t))?;
                state.raw_defs.push(TopLevel::TLExternDef(
                    name,
                    self.arena.alloc_slice(&core_params),
                    core_ret,
                    span.clone(),
                ));
                continue;
            }
            if let TopLevel::TLDef(name, params, m_ret, body_term, span) = logical_top {
                if Self::is_compiler_replaced_top(top, name) {
                    continue;
                }
                if m_ret.is_some_and(Self::is_meta_codegen_constraint) {
                    continue;
                }
                if matches!(body_term, Term::EnumDef(..) | Term::StructDef(..)) {
                    continue;
                }
                let desugared = self.desugar_checked_def(params, *m_ret, *body_term)?;
                let resolved = self.subst_top_level(desugared);
                let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
                let core_params = params
                    .iter()
                    .enumerate()
                    .map(|(idx, (pn, mc))| {
                        let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
                        Ok((
                            *pn,
                            mc.map(|t| self.checker.desugar_with_names_context(t, &dom_env))
                                .map(|r| r.map(|t| self.normalize_codegen_constraint(t)))
                                .transpose()?,
                        ))
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                let core_ret = m_ret
                    .map(|t| self.checker.desugar_with_names_context(t, &names))
                    .map(|r| r.map(|t| self.normalize_codegen_constraint(t)))
                    .transpose()?;
                state.raw_defs.push(TopLevel::TLDef(
                    name,
                    self.arena.alloc_slice(&core_params),
                    core_ret,
                    resolved,
                    span.clone(),
                ));
            }
        }
        Ok(state)
    }

    /// Erase, resolve, and filter top-level definitions. Skips enum/struct
    /// typedefs (including generic ones) and drops zero-param type aliases after erasure.
    pub(crate) fn erase_and_collect_tops(
        &self,
        tops: Vec<TopLevel<'bump>>,
        raw_defs: &[TopLevel<'bump>],
        eraser: &Eraser<'bump>,
    ) -> Result<ErasedProgram<'bump>, Diagnostic> {
        let tops = tops
            .into_iter()
            .map(|top| match top {
                TopLevel::TLAttributed(_, inner, _) => {
                    if top.has_attribute(COMPILER_INTRINSIC_ATTR) {
                        Ok(None)
                    } else {
                        self.erase_top_for_codegen((*inner).clone(), raw_defs, eraser)
                    }
                }
                other => self.erase_top_for_codegen(other, raw_defs, eraser),
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?
            .into_iter()
            .flatten()
            .filter(|top| {
                !matches!(
                    top,
                    TopLevel::TLDef(_, params, _, body, _)
                        if params.is_empty()
                            && matches!(body, Term::Builtin(_) | Term::Global(_) | Term::EnumDef(..) | Term::StructDef(..))
                )
            })
            .collect();
        Ok(ErasedProgram { tops })
    }

    fn erase_top_for_codegen(
        &self,
        top: TopLevel<'bump>,
        raw_defs: &[TopLevel<'bump>],
        eraser: &Eraser<'bump>,
    ) -> Result<Option<TopLevel<'bump>>, Diagnostic> {
        match top {
            TopLevel::TLDef(_name, _params, _m_ret, Term::EnumDef(..) | Term::StructDef(..), _) => {
                Ok(None)
            }
            TopLevel::TLDef(name, params, m_ret, body_term, span) => {
                if crate::config::is_std_intrinsic_name(name) {
                    return Ok(None);
                }
                if m_ret.is_some_and(Self::is_meta_codegen_constraint) {
                    return Ok(None);
                }
                if name.starts_with(crate::config::GLOBAL_ALLOCATOR_NAME_PREFIX) {
                    return Ok(None);
                }
                let semantics = SemanticQueries::new(self.checker.builtins());
                if params
                    .iter()
                    .any(|(_, c)| c.is_some_and(|t| semantics.is_erased_parameter_constraint(t)))
                {
                    return Ok(None);
                }
                let erased = if Self::contains_surface_codegen_syntax(body_term) {
                    if let Some(raw_body) = raw_defs.iter().find_map(|top| match top {
                        TopLevel::TLDef(raw_name, _, _, raw_body, _) if *raw_name == name => {
                            Some(*raw_body)
                        }
                        _ => None,
                    }) {
                        let desugared = self.desugar_checked_def(params, m_ret, raw_body)?;
                        let resolved = self.subst_top_level(desugared);
                        let resolved =
                            self.elaborate_of_nat_literals(resolved, &empty_ctx(), None)?;
                        eraser.erase(resolved)
                    } else {
                        let desugared = self.desugar_checked_def(params, m_ret, body_term)?;
                        let resolved = self.subst_top_level(desugared);
                        let resolved =
                            self.elaborate_of_nat_literals(resolved, &empty_ctx(), None)?;
                        eraser.erase(resolved)
                    }
                } else {
                    let desugared = self.checker.desugar_with_context(body_term).or_else(|_| {
                        let term = self.env.get(name).copied().unwrap_or(body_term);
                        self.checker.desugar_with_context(term)
                    })?;
                    let resolved = self.subst_top_level(desugared);
                    let resolved =
                        self.elaborate_of_nat_literals(resolved, &empty_ctx(), None)?;
                    eraser.erase(resolved)
                };
                Ok(Some(TopLevel::TLDef(name, params, m_ret, erased, span)))
            }
            TopLevel::TLEval(term, span) => {
                let desugared = self.checker.desugar_with_context(term)?;
                let resolved = self.subst_top_level(desugared);
                let resolved = self.elaborate_of_nat_literals(resolved, &empty_ctx(), None)?;
                Ok(Some(TopLevel::TLEval(eraser.erase(resolved), span)))
            }
            TopLevel::TLExpr(term, span) => {
                let desugared = self.checker.desugar_with_context(term)?;
                let resolved = self.subst_top_level(desugared);
                let resolved = self.elaborate_of_nat_literals(resolved, &empty_ctx(), None)?;
                Ok(Some(TopLevel::TLExpr(eraser.erase(resolved), span)))
            }
            TopLevel::TLTheorem(name, _, body, span) => {
                let resolved_body = self.try_resolve_all(body)?;
                let erased = eraser.erase(resolved_body);
                Ok(Some(TopLevel::TLDef(name, &[], None, erased, span)))
            }
            TopLevel::TLExternDef(..) => Ok(None),
            TopLevel::TLInstance(..) => Ok(None),
            TopLevel::TLVariable(..) => Ok(None),
            TopLevel::TLUse(..)
            | TopLevel::TLMod(..)
            | TopLevel::TLNamespace(..)
            | TopLevel::TLSplice(..) => Ok(None),
            TopLevel::TLPublic(inner) => {
                self.erase_top_for_codegen((*inner).clone(), raw_defs, eraser)
            }
            TopLevel::TLCheck(_, _, _) => Ok(None),
            TopLevel::TLAttributed(_, inner, _) => {
                self.erase_top_for_codegen((*inner).clone(), raw_defs, eraser)
            }
        }
    }

    fn logical_codegen_top<'top>(top: &'top TopLevel<'bump>) -> &'top TopLevel<'bump> {
        let mut top = top;
        loop {
            match top {
                TopLevel::TLAttributed(_, inner, _) | TopLevel::TLPublic(inner) => top = inner,
                other => return other,
            }
        }
    }

    fn is_compiler_replaced_top(top: &TopLevel<'bump>, name: &str) -> bool {
        top.has_attribute(COMPILER_INTRINSIC_ATTR) || crate::config::is_std_intrinsic_name(name)
    }

    fn is_meta_codegen_constraint(term: &Term<'_>) -> bool {
        match term {
            Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
                crate::config::canonical_builtin_name(name) == crate::compiler::meta::EXPR_TYPE
                    || crate::config::canonical_builtin_name(name)
                        == crate::compiler::meta::DEFINITIONS_TYPE
            }
            Term::Annot(inner, _) | Term::Implicit(inner) => {
                Self::is_meta_codegen_constraint(inner)
            }
            _ => false,
        }
    }

    fn normalize_codegen_type_def(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match term {
            Term::EnumDef(name, variants) => {
                let variants = variants
                    .iter()
                    .map(|(variant_name, fields)| {
                        let fields = fields
                            .iter()
                            .map(|(field_name, constraint)| {
                                (*field_name, self.normalize_codegen_constraint(constraint))
                            })
                            .collect::<Vec<_>>();
                        (*variant_name, self.arena.alloc_slice(&fields))
                    })
                    .collect::<Vec<_>>();
                self.arena.enum_def(name, self.arena.alloc_slice(&variants))
            }
            Term::StructDef(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field_name, constraint)| {
                        (*field_name, self.normalize_codegen_constraint(constraint))
                    })
                    .collect::<Vec<_>>();
                self.arena.struct_def(name, self.arena.alloc_slice(&fields))
            }
            _ => term,
        }
    }

    fn is_erased_interface_struct(term: &Term<'_>) -> bool {
        let Term::StructDef(_, fields) = term else {
            return false;
        };
        fields
            .iter()
            .any(|(_, constraint)| Self::contains_pi_constraint(constraint))
    }

    fn contains_surface_codegen_syntax(term: &Term<'_>) -> bool {
        match term {
            Term::Named(_)
            | Term::NamedLam(..)
            | Term::NamedMatch(..)
            | Term::MethodCall(..)
            | Term::Do(_) => true,
            Term::App(f, a) | Term::Annot(f, a) | Term::Pi(_, f, a) => {
                Self::contains_surface_codegen_syntax(f) || Self::contains_surface_codegen_syntax(a)
            }
            Term::Implicit(inner)
            | Term::Lam(inner)
            | Term::Unsafe(inner)
            | Term::Pure(inner)
            | Term::Quote(inner)
            | Term::Splice(inner) => Self::contains_surface_codegen_syntax(inner),
            Term::Let(_, val, body, constraint) => {
                Self::contains_surface_codegen_syntax(val)
                    || Self::contains_surface_codegen_syntax(body)
                    || constraint.is_some_and(Self::contains_surface_codegen_syntax)
            }
            Term::IfThenElse(cond, then_term, else_term) => {
                Self::contains_surface_codegen_syntax(cond)
                    || Self::contains_surface_codegen_syntax(then_term)
                    || Self::contains_surface_codegen_syntax(else_term)
            }
            Term::ByProof(inner, tactics) => {
                inner.is_some_and(Self::contains_surface_codegen_syntax)
                    || tactics.iter().any(|tactic| match tactic {
                        crate::core::syntax::Tactic::Exact(term)
                        | crate::core::syntax::Tactic::Apply(term)
                        | crate::core::syntax::Tactic::Have(_, term) => {
                            Self::contains_surface_codegen_syntax(term)
                        }
                        crate::core::syntax::Tactic::Custom(_, args) => args
                            .iter()
                            .any(|arg| Self::contains_surface_codegen_syntax(arg)),
                        crate::core::syntax::Tactic::Intro(_) => false,
                    })
            }
            Term::EnumDef(_, variants) => variants.iter().any(|(_, fields)| {
                fields
                    .iter()
                    .any(|(_, constraint)| Self::contains_surface_codegen_syntax(constraint))
            }),
            Term::Variant(_, _, payloads) | Term::StructCons(_, payloads) => payloads
                .iter()
                .any(|payload| Self::contains_surface_codegen_syntax(payload)),
            Term::Match(scrutinee, branches) => {
                Self::contains_surface_codegen_syntax(scrutinee)
                    || branches.iter().any(|(_, binds, body)| {
                        binds.iter().any(|(_, constraint)| {
                            Self::contains_surface_codegen_syntax(constraint)
                        }) || Self::contains_surface_codegen_syntax(body)
                    })
            }
            Term::StructDef(_, fields) => fields
                .iter()
                .any(|(_, constraint)| Self::contains_surface_codegen_syntax(constraint)),
            Term::StructProj(subject, _) => Self::contains_surface_codegen_syntax(subject),
            _ => false,
        }
    }

    fn contains_pi_constraint(term: &Term<'_>) -> bool {
        match term {
            Term::Pi(..) => true,
            Term::Annot(inner, constraint) | Term::App(inner, constraint) => {
                Self::contains_pi_constraint(inner) || Self::contains_pi_constraint(constraint)
            }
            Term::Implicit(inner) | Term::Unsafe(inner) | Term::Pure(inner) => {
                Self::contains_pi_constraint(inner)
            }
            _ => false,
        }
    }

    fn normalize_codegen_constraint(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match term {
            Term::Builtin(name) | Term::Global(name) => lookup_refine(name, self.checker.table())
                .map(|(parent, _)| self.normalize_codegen_constraint(parent))
                .unwrap_or(term),
            Term::Refine(name, parent, predicate) => {
                self.arena
                    .refine(name, self.normalize_codegen_constraint(parent), predicate)
            }
            Term::Annot(inner, constraint) => self
                .arena
                .annot(inner, self.normalize_codegen_constraint(constraint)),
            Term::Unsafe(inner) => self.arena.unsafe_(self.normalize_codegen_constraint(inner)),
            Term::Pure(inner) => self.arena.pure(self.normalize_codegen_constraint(inner)),
            _ => term,
        }
    }

    fn apply_codegen_state(&mut self, state: CodegenState<'bump>) {
        self.raw_defs = state.raw_defs;
        self.fun_sigs = state.fun_sigs;
        self.enum_types = state.enum_types;
        self.struct_types = state.struct_types;
    }
}
