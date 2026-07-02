//! Main C code emitter — the orchestrator.
//!
//! `CEmitter` is the central coordinator for C code generation.  It
//! aggregates all sub-components (`TypeAnalyzer`, `NameResolver`,
//! `ExpressionEmitter`, `MatchEmitter`) and implements the `CodeGenerator`
//! trait, following the OOP composite pattern.

use crate::backend::c::context::EmitCtx;
use crate::backend::c::expr::ExpressionEmitter;
use crate::backend::c::match_emit::MatchEmitter;
use crate::backend::c::names::NameResolver;
use crate::backend::c::types::{TypeAnalyzer, TypeMapper};
use crate::backend::c::value::CExpr;
use crate::backend::ir::{CType, FunSig};
use crate::config::GLOBAL_ALLOCATOR_NAME_PREFIX;
use crate::core::syntax::{Name, PrimOp, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::TopLevel;
use std::collections::HashSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CTarget {
    Hosted,
    BareMetal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CEmitOptions {
    pub target: CTarget,
}

impl Default for CEmitOptions {
    fn default() -> Self {
        Self {
            target: CTarget::Hosted,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct GlobalAllocator {
    pub(crate) allocate: String,
    pub(crate) deallocate: String,
    pub(crate) reallocate: String,
    pub(crate) is_default: bool,
}

impl GlobalAllocator {
    fn hosted_default() -> Self {
        Self {
            allocate: "ligare_default_allocate".into(),
            deallocate: "ligare_default_deallocate".into(),
            reallocate: "ligare_default_reallocate".into(),
            is_default: true,
        }
    }
}

/// Generates complete C source code from Ligare top-level items.
///
/// This trait is the public contract for code generation — different
/// backends can implement it for different target languages.
pub trait CodeGenerator {
    /// Generate a complete source file.
    fn generate(
        &self,
        tops: &[TopLevel<'_>],
        raw_defs: &[TopLevel<'_>],
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
    ) -> Result<String, Diagnostic>;

    /// Generate an eval-only helper source file.
    fn generate_eval(
        &self,
        tops: &[TopLevel<'_>],
        raw_defs: &[TopLevel<'_>],
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
    ) -> Result<Option<String>, Diagnostic>;
}

/// The C code emitter — orchestrates all sub-components.
///
/// Follows the OOP composite pattern:
/// - `type_analyzer` owns the type maps and handles typedef emission
/// - `name_resolver` handles escaping and on-demand name collection
/// - `expr_emitter` handles expression → C translation (stateless service)
/// - `match_emitter` handles match → switch translation
/// - `fun_sigs` provides return-type inference for function calls
pub struct CEmitter<'a> {
    /// Function signatures for type inference.
    fun_sigs: &'a [(&'a str, FunSig)],
    /// Type analysis and typedef emission.
    type_analyzer: TypeAnalyzer,
    /// Name resolution and escaping.
    name_resolver: NameResolver,
    /// Expression translation (stateless service object).
    expr_emitter: ExpressionEmitter<'a>,
    /// Match block translation.
    match_emitter: MatchEmitter,
    /// Target-specific code generation options.
    options: CEmitOptions,
}

impl<'a> CEmitter<'a> {
    /// Create a new emitter from the compilation context.
    ///
    /// Builds all sub-components and wires them together.
    pub fn new(
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
        fun_sigs: &'a [(&'a str, FunSig)],
    ) -> Result<Self, Diagnostic> {
        Self::new_with_options(struct_types, enum_types, fun_sigs, CEmitOptions::default())
    }

    pub fn new_with_options(
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
        fun_sigs: &'a [(&'a str, FunSig)],
        options: CEmitOptions,
    ) -> Result<Self, Diagnostic> {
        let type_analyzer = TypeAnalyzer::new(struct_types, enum_types)?;
        let expr_emitter = ExpressionEmitter::new(fun_sigs);
        Ok(Self {
            fun_sigs,
            type_analyzer,
            name_resolver: NameResolver::new(),
            expr_emitter,
            match_emitter: MatchEmitter::new(),
            options,
        })
    }

    // ── Definition emission ──

    /// Emit a top-level definition as a C function or constant.
    fn emit_def(
        &self,
        name: &str,
        params: &[(Name<'_>, Option<&Term<'_>>)],
        body: &Term<'_>,
    ) -> Result<String, Diagnostic> {
        if params.is_empty() {
            let arity = self.name_resolver.count_lams(body);
            if arity == 0 {
                let mut ctx = EmitCtx::new();
                let value = self.expr_emitter.emit_expr(
                    body,
                    &mut ctx,
                    self.type_analyzer.enum_map(),
                    self.type_analyzer.struct_map(),
                )?;
                let code = value.expr.code()?;
                Ok(format!(
                    "const {} {} = {};\n",
                    value.ctype.c_name(),
                    self.name_resolver.escape(name),
                    code.as_str()
                ))
            } else {
                Err(Diagnostic::new(format!(
                    "Cannot emit function `{name}` without explicit parameter types"
                )))
            }
        } else {
            // Filter out erased generic params.
            let data_params: Vec<_> = params
                .iter()
                .filter(|(_, mc)| {
                    !mc.is_some_and(|c| self.type_analyzer.is_erased_parameter_constraint(c))
                })
                .collect();
            let pns: Vec<String> = data_params
                .iter()
                .map(|(n, _)| self.name_resolver.escape(n))
                .collect();
            let param_types: Vec<CType> = self
                .fun_sigs
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, sig)| sig.param_types.clone())
                .ok_or_else(|| {
                    Diagnostic::new(format!(
                        "Cannot emit function `{name}`; missing function signature"
                    ))
                })?;
            let peeled = self.name_resolver.peel_lams(body, params.len());
            self.emit_fun(name, &pns, &param_types, peeled)
        }
    }

    /// Emit a C function with named parameters and a Term body.
    fn emit_fun(
        &self,
        name: &str,
        params: &[String],
        param_types: &[CType],
        body: &Term<'_>,
    ) -> Result<String, Diagnostic> {
        let cps: Vec<String> = params
            .iter()
            .zip(param_types.iter())
            .map(|(p, ty)| format!("{} {}", ty.c_name(), self.name_resolver.escape(p)))
            .collect();
        let mut ctx = EmitCtx::from_params(params, param_types);
        ctx.self_name = Some(name.to_string());
        let body_value = self.expr_emitter.emit_expr(
            body,
            &mut ctx,
            self.type_analyzer.enum_map(),
            self.type_analyzer.struct_map(),
        )?;
        let return_stmt = match body_value.expr {
            CExpr::Match(plan) => {
                let block = self
                    .match_emitter
                    .emit(&plan, 0, self.type_analyzer.enum_map());
                format!("{block}    return {};\n", self.name_resolver.result_temp(0))
            }
            CExpr::Code(code) => format!("    return {};\n", code.as_str()),
        };
        Ok(format!(
            "{} {}({}) {{\n{}}}\n",
            body_value.ctype.c_name(),
            self.name_resolver.escape(name),
            cps.join(", "),
            return_stmt
        ))
    }

    /// Emit a printf statement for the given expression and C type.
    fn emit_printf(&self, out: &mut String, expr: &str, ctype: &CType) {
        match ctype {
            CType::Str => out.push_str(&format!("    printf(\"%s\\n\", {});\n", expr)),
            CType::Int64
            | CType::Int8
            | CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::UInt64
            | CType::CInt
            | CType::CUInt => {
                out.push_str(&format!("    printf(\"%ld\\n\", (int64_t)({}));\n", expr))
            }
            CType::Ptr(_) => out.push_str(&format!("    printf(\"%p\\n\", (void*)({}));\n", expr)),
            CType::Enum(_) => out.push_str(&format!("    printf(\"%d\\n\", ({}).tag);\n", expr)),
            CType::Struct(_) => out.push_str("    printf(\"<struct>\\n\");\n"),
        }
    }

    fn collect_outputs<'t>(
        &self,
        tops: &'t [TopLevel<'_>],
        include_eval: bool,
        include_expr: bool,
    ) -> Vec<&'t Term<'t>> {
        let mut outputs = Vec::new();
        for top in tops {
            match top {
                TopLevel::TLEval(term, _) if include_eval => outputs.push(*term),
                TopLevel::TLExpr(term, _) if include_expr => outputs.push(*term),
                _ => {}
            }
        }
        outputs
    }

    fn resolve_global_allocator(
        &self,
        raw_defs: &[TopLevel<'_>],
        allocation_required: bool,
    ) -> Result<Option<GlobalAllocator>, Diagnostic> {
        let mut found = Vec::new();
        for raw_def in raw_defs {
            let TopLevel::TLDef(name, _params, _ret, body, _) = raw_def else {
                continue;
            };
            if !name.starts_with(GLOBAL_ALLOCATOR_NAME_PREFIX) {
                continue;
            }
            found.push((*name, *body));
        }
        if found.len() > 1 {
            return Err(Diagnostic::new(
                "multiple #[global_allocator] definitions are not allowed",
            ));
        }
        if let Some((encoded_name, body)) = found.into_iter().next() {
            return self.allocator_from_definition(encoded_name, body).map(Some);
        }
        if !allocation_required {
            return Ok(None);
        }
        match self.options.target {
            CTarget::Hosted => Ok(Some(GlobalAllocator::hosted_default())),
            CTarget::BareMetal => Err(Diagnostic::new(
                "bare-metal target requires an explicit #[global_allocator]",
            )),
        }
    }

    fn allocator_from_definition(
        &self,
        encoded_name: &str,
        body: &Term<'_>,
    ) -> Result<GlobalAllocator, Diagnostic> {
        let instance_name = encoded_name
            .strip_prefix(GLOBAL_ALLOCATOR_NAME_PREFIX)
            .unwrap_or(encoded_name);
        let body = self.peel_annotations(body);
        let Term::StructCons(_, fields) = body else {
            return Ok(GlobalAllocator {
                allocate: self
                    .name_resolver
                    .escape(&format!("{instance_name}_allocate")),
                deallocate: self
                    .name_resolver
                    .escape(&format!("{instance_name}_deallocate")),
                reallocate: self
                    .name_resolver
                    .escape(&format!("{instance_name}_reallocate")),
                is_default: false,
            });
        };
        if fields.len() < 3 {
            return Err(Diagnostic::new(format!(
                "#[global_allocator] `{instance_name}` must provide allocate, deallocate, and reallocate"
            )));
        }
        Ok(GlobalAllocator {
            allocate: self.allocator_field_name(fields[0], "allocate")?,
            deallocate: self.allocator_field_name(fields[1], "deallocate")?,
            reallocate: self.allocator_field_name(fields[2], "reallocate")?,
            is_default: false,
        })
    }

    fn peel_annotations<'t>(&self, mut term: &'t Term<'t>) -> &'t Term<'t> {
        while let Term::Annot(inner, _) | Term::Unsafe(inner) | Term::Pure(inner) = term {
            term = inner;
        }
        term
    }

    fn allocator_field_name(&self, term: &Term<'_>, field: &str) -> Result<String, Diagnostic> {
        match self.peel_annotations(term) {
            Term::Builtin(name) | Term::Global(name) => Ok(self.name_resolver.escape(name)),
            other => Err(Diagnostic::new(format!(
                "#[global_allocator] field `{field}` must be a direct function name, got {other:?}"
            ))),
        }
    }

    fn term_requires_allocation(&self, term: &Term<'_>) -> bool {
        match term {
            Term::App(f, _)
                if self.is_string_concat_app(term) || self.term_requires_allocation(f) =>
            {
                true
            }
            Term::App(f, a) => self.term_requires_allocation(f) || self.term_requires_allocation(a),
            Term::Let(_, val, body, c) => {
                self.term_requires_allocation(val)
                    || self.term_requires_allocation(body)
                    || c.is_some_and(|c| self.term_requires_allocation(c))
            }
            Term::IfThenElse(c, t, f) => {
                self.term_requires_allocation(c)
                    || self.term_requires_allocation(t)
                    || self.term_requires_allocation(f)
            }
            Term::Annot(inner, c) => {
                self.term_requires_allocation(inner) || self.term_requires_allocation(c)
            }
            Term::Unsafe(inner) | Term::Pure(inner) | Term::Lam(inner) => {
                self.term_requires_allocation(inner)
            }
            Term::StructCons(_, values) => values
                .iter()
                .any(|value| self.term_requires_allocation(value)),
            Term::Variant(uname, idx, values) => {
                self.variant_requires_heap_payload(uname, *idx)
                    || values
                        .iter()
                        .any(|value| self.term_requires_allocation(value))
            }
            Term::StructProj(subject, _) => self.term_requires_allocation(subject),
            Term::Match(scrut, branches) => {
                self.term_requires_allocation(scrut)
                    || branches.iter().any(|(_, binds, body)| {
                        self.term_requires_allocation(body)
                            || binds.iter().any(|(_, c)| self.term_requires_allocation(c))
                    })
            }
            _ => false,
        }
    }

    fn variant_requires_heap_payload(&self, uname: &str, idx: usize) -> bool {
        self.type_analyzer
            .enum_map()
            .get(uname)
            .and_then(|info| info.variants.get(idx))
            .is_some_and(|variant| {
                variant.fields.iter().any(|(_, cty)| {
                    matches!(cty, CType::Ptr(inner) if matches!(inner.as_ref(), CType::Enum(inner_name) if inner_name == uname))
                })
            })
    }

    fn is_string_concat_app(&self, term: &Term<'_>) -> bool {
        let Term::App(f, right) = term else {
            return false;
        };
        let Term::App(prim, left) = *f else {
            return false;
        };
        matches!(*prim, Term::PrimOp(PrimOp::Add))
            && self.term_is_string_like(left)
            && self.term_is_string_like(right)
    }

    fn term_is_string_like(&self, term: &Term<'_>) -> bool {
        match term {
            Term::LitStr(_) => true,
            Term::Annot(_, constraint) => {
                matches!(**constraint, Term::Builtin("str") | Term::Global("str"))
            }
            Term::Unsafe(inner) | Term::Pure(inner) => self.term_is_string_like(inner),
            Term::App(f, _) if self.is_string_concat_app(term) => true,
            Term::Builtin(name) | Term::Global(name) => self
                .fun_sigs
                .iter()
                .find(|(n, _)| *n == *name)
                .is_some_and(|(_, sig)| sig.ret_type == CType::Str),
            _ => false,
        }
    }

    fn emit_default_allocator(out: &mut String) {
        out.push_str(
            "static void* ligare_default_allocate(size_t size) { return malloc(size); }\n",
        );
        out.push_str("static void ligare_default_deallocate(void* ptr) { free(ptr); }\n");
        out.push_str(
            "static void* ligare_default_reallocate(void* ptr, size_t size) { return realloc(ptr, size); }\n\n",
        );
    }

    fn generate_with_outputs(
        &self,
        tops: &[TopLevel<'_>],
        raw_defs: &[TopLevel<'_>],
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
        outputs: &[&Term<'_>],
    ) -> Result<String, Diagnostic> {
        let mut called_names: HashSet<String> = if outputs.is_empty() {
            self.name_resolver.all_def_names(raw_defs)
        } else {
            self.name_resolver.collect_called_names(outputs, raw_defs)
        };
        let allocation_required =
            self.codegen_roots_require_allocation(tops, raw_defs, outputs, &called_names);
        let allocator = self.resolve_global_allocator(raw_defs, allocation_required)?;
        self.expr_emitter.set_global_allocator(allocator.clone());
        if let Some(allocator) = &allocator
            && !allocator.is_default
        {
            called_names.insert(allocator.allocate.clone());
            called_names.insert(allocator.deallocate.clone());
            called_names.insert(allocator.reallocate.clone());
        }

        let mut out =
            String::from("#include <stdio.h>\n#include <stdint.h>\n#include <stddef.h>\n");
        if allocator
            .as_ref()
            .is_some_and(|allocator| allocator.is_default)
        {
            out.push_str("#include <stdlib.h>\n");
        }
        out.push('\n');
        if allocator
            .as_ref()
            .is_some_and(|allocator| allocator.is_default)
        {
            Self::emit_default_allocator(&mut out);
        }

        self.type_analyzer
            .emit_type_declarations(&mut out, struct_types, enum_types)?;

        for (name, sig) in self.fun_sigs {
            if self.name_resolver.is_extern_name(name, raw_defs) {
                let params = sig
                    .param_types
                    .iter()
                    .map(CType::c_name)
                    .collect::<Vec<_>>()
                    .join(", ");
                out.push_str(&format!(
                    "extern {} {}({});\n",
                    sig.ret_type.c_name(),
                    self.name_resolver.escape(name),
                    params
                ));
            }
        }
        if self
            .fun_sigs
            .iter()
            .any(|(name, _)| self.name_resolver.is_extern_name(name, raw_defs))
        {
            out.push('\n');
        }

        for top in tops {
            if let TopLevel::TLDef(name, params, _m_ret, body, _) = top
                && params.is_empty()
                && self.name_resolver.count_lams(body) == 0
                && *name != "main"
            {
                out.push_str(&self.emit_def(name, params, body)?);
                out.push('\n');
            }
        }

        for raw_def in raw_defs {
            if let TopLevel::TLDef(name, params, _m_ret, body, _) = raw_def {
                if name.starts_with(GLOBAL_ALLOCATOR_NAME_PREFIX) {
                    continue;
                }
                if *name == "main" || params.is_empty() && self.name_resolver.count_lams(body) == 0
                {
                    continue;
                }
                if called_names.contains(*name) {
                    out.push_str(&self.emit_def(name, params, body)?);
                    out.push('\n');
                }
            }
        }

        out.push_str("int main(void) {\n");
        let mut match_counter: u32 = 0;
        if let Some(main_body) = self.runtime_main_body(tops) {
            let mut ctx = EmitCtx::new();
            let value = self.expr_emitter.emit_expr(
                main_body,
                &mut ctx,
                self.type_analyzer.enum_map(),
                self.type_analyzer.struct_map(),
            )?;
            match value.expr {
                CExpr::Match(plan) => {
                    let block = self.match_emitter.emit(
                        &plan,
                        match_counter,
                        self.type_analyzer.enum_map(),
                    );
                    match_counter += 1;
                    out.push_str(&block);
                }
                CExpr::Code(code) => out.push_str(&format!("    (void)({});\n", code.as_str())),
            }
        }
        for term in outputs {
            let mut ctx = EmitCtx::new();
            let value = self.expr_emitter.emit_expr(
                term,
                &mut ctx,
                self.type_analyzer.enum_map(),
                self.type_analyzer.struct_map(),
            )?;
            match value.expr {
                CExpr::Match(plan) => {
                    let block = self.match_emitter.emit(
                        &plan,
                        match_counter,
                        self.type_analyzer.enum_map(),
                    );
                    match_counter += 1;
                    out.push_str(&block);
                    let r_var = self.name_resolver.result_temp(match_counter - 1);
                    self.emit_printf(&mut out, &r_var, &value.ctype);
                }
                CExpr::Code(code) => self.emit_printf(&mut out, code.as_str(), &value.ctype),
            }
        }
        out.push_str("    return 0;\n}\n");
        Ok(out)
    }

    fn codegen_roots_require_allocation(
        &self,
        tops: &[TopLevel<'_>],
        raw_defs: &[TopLevel<'_>],
        outputs: &[&Term<'_>],
        called_names: &HashSet<String>,
    ) -> bool {
        outputs
            .iter()
            .any(|term| self.term_requires_allocation(term))
            || self
                .runtime_main_body(tops)
                .is_some_and(|body| self.term_requires_allocation(body))
            || tops.iter().any(|top| {
                matches!(
                    top,
                    TopLevel::TLDef(name, params, _, body, _)
                        if *name != "main"
                            && params.is_empty()
                            && self.name_resolver.count_lams(body) == 0
                            && self.term_requires_allocation(body)
                )
            })
            || raw_defs.iter().any(|top| {
                matches!(
                    top,
                    TopLevel::TLDef(name, _, _, body, _)
                        if called_names.contains(*name) && self.term_requires_allocation(body)
                )
            })
    }

    fn runtime_main_body<'t>(&self, tops: &'t [TopLevel<'_>]) -> Option<&'t Term<'t>> {
        tops.iter().find_map(|top| {
            if let TopLevel::TLDef(name, params, _ret, body, _) = top
                && *name == "main"
                && params.is_empty()
                && self.name_resolver.count_lams(body) == 0
            {
                Some(*body)
            } else {
                None
            }
        })
    }
}

impl<'a> CodeGenerator for CEmitter<'a> {
    fn generate(
        &self,
        tops: &[TopLevel<'_>],
        raw_defs: &[TopLevel<'_>],
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
    ) -> Result<String, Diagnostic> {
        let outputs = self.collect_outputs(tops, false, true);
        self.generate_with_outputs(tops, raw_defs, struct_types, enum_types, &outputs)
    }

    fn generate_eval(
        &self,
        tops: &[TopLevel<'_>],
        raw_defs: &[TopLevel<'_>],
        struct_types: &[(&str, &Term<'_>)],
        enum_types: &[(&str, &Term<'_>)],
    ) -> Result<Option<String>, Diagnostic> {
        let outputs = self.collect_outputs(tops, true, false);
        if outputs.is_empty() {
            return Ok(None);
        }
        self.generate_with_outputs(tops, raw_defs, struct_types, enum_types, &outputs)
            .map(Some)
    }
}
