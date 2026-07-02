use crate::checker::context::lookup_refine;
use crate::checker::erase::Eraser;
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
    pub(crate) union_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    pub(crate) struct_types: Vec<(&'bump str, &'bump Term<'bump>)>,
}

impl<'bump> CodegenState<'bump> {
    pub(crate) fn empty() -> Self {
        Self {
            raw_defs: Vec::new(),
            fun_sigs: Vec::new(),
            union_types: Vec::new(),
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
        for top in &parsed.tops {
            self.process_top_level(top.clone())
                .map_err(|d| d.with_source_if_missing(file, content))?;
        }
        let codegen = self.collect_codegen_state(&parsed.tops)?;
        let monomorphized = self.monomorphize_for_codegen(parsed.tops, codegen)?;
        self.apply_codegen_state(monomorphized.codegen);

        let eraser = Eraser::new(self.arena, self.checker.builtins.clone());
        let erased = self.erase_and_collect_tops(monomorphized.tops, &eraser)?;
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

    /// Collect the codegen-facing inputs from the original un-erased tops.
    pub(crate) fn collect_codegen_state(
        &self,
        tops: &[TopLevel<'bump>],
    ) -> Result<CodegenState<'bump>, Diagnostic> {
        let mut state = CodegenState::empty();
        for top in tops {
            if let TopLevel::TLDef(name, params, _m_ret, body, _) = top {
                let name = self.codegen_attribute_target_name(name);
                let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
                if matches!(body, Term::UnionDef(..)) {
                    let body = self.checker.desugar_with_names_context(body, &names)?;
                    let body = self.normalize_codegen_type_def(body);
                    state.union_types.push((name, body));
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
            if let TopLevel::TLExternDef(name, params, ret, span) = top {
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
            if let TopLevel::TLDef(name, params, m_ret, body_term, span) = top {
                if matches!(body_term, Term::UnionDef(..) | Term::StructDef(..)) {
                    continue;
                }
                let actual_name = self.codegen_attribute_target_name(name);
                let term = self.env.get(actual_name).copied().unwrap_or(*body_term);
                let desugared = self.checker.desugar_with_context(term)?;
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

    /// Erase, resolve, and filter top-level definitions. Skips union/struct
    /// typedefs (including generic ones) and drops zero-param type aliases after erasure.
    pub(crate) fn erase_and_collect_tops(
        &self,
        tops: Vec<TopLevel<'bump>>,
        eraser: &Eraser<'bump>,
    ) -> Result<ErasedProgram<'bump>, Diagnostic> {
        let tops = tops
            .into_iter()
            .map(|top| match top {
                TopLevel::TLDef(
                    _name,
                    _params,
                    _m_ret,
                    Term::UnionDef(..) | Term::StructDef(..),
                    _,
                ) => Ok(None),
                TopLevel::TLDef(name, params, m_ret, body_term, span) => {
                    if name.starts_with(crate::config::GLOBAL_ALLOCATOR_NAME_PREFIX) {
                        return Ok(None);
                    }
                    let semantics = SemanticQueries::new(self.checker.builtins());
                    if params.iter().any(|(_, c)| {
                        c.is_some_and(|t| semantics.is_erased_parameter_constraint(t))
                    }) {
                        return Ok(None);
                    }
                    let desugared = self
                        .checker
                        .desugar_with_context(body_term)
                        .or_else(|_| {
                            let term = self.env.get(name).copied().unwrap_or(body_term);
                            self.checker.desugar_with_context(term)
                        })?;
                    let resolved = self.subst_top_level(desugared);
                    let desugared = self.checker.desugar_with_context(resolved)?;
                    let erased = eraser.erase(desugared);
                    Ok(Some(TopLevel::TLDef(name, params, m_ret, erased, span)))
                }
                TopLevel::TLEval(term, span) => {
                    let desugared = self.checker.desugar_with_context(term)?;
                    let resolved = self.subst_top_level(desugared);
                    Ok(Some(TopLevel::TLEval(eraser.erase(resolved), span)))
                }
                TopLevel::TLExpr(term, span) => {
                    let desugared = self.checker.desugar_with_context(term)?;
                    let resolved = self.subst_top_level(desugared);
                    Ok(Some(TopLevel::TLExpr(eraser.erase(resolved), span)))
                }
                TopLevel::TLTheorem(name, _, body, span) => {
                    let resolved_body = self.try_resolve_all(body)?;
                    let erased = eraser.erase(resolved_body);
                    Ok(Some(TopLevel::TLDef(name, &[], None, erased, span)))
                }
                TopLevel::TLExternDef(..) => Ok(None),
                TopLevel::TLInstance(..) => Ok(None),
                TopLevel::TLUse(..) | TopLevel::TLMod(..) | TopLevel::TLPublic(_) => Ok(None),
                TopLevel::TLCheck(_, _, _) => Ok(None),
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?
            .into_iter()
            .flatten()
            .filter(|top| {
                !matches!(
                    top,
                    TopLevel::TLDef(_, params, _, body, _)
                        if params.is_empty()
                            && matches!(body, Term::Builtin(_) | Term::Global(_) | Term::UnionDef(..) | Term::StructDef(..))
                )
            })
            .collect();
        Ok(ErasedProgram { tops })
    }

    fn normalize_codegen_type_def(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match term {
            Term::UnionDef(name, variants) => {
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
                self.arena
                    .union_def(name, self.arena.alloc_slice(&variants))
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
        self.union_types = state.union_types;
        self.struct_types = state.struct_types;
    }
}
