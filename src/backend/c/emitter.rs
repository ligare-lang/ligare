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
use crate::backend::c::types::{EnumInfo, StructInfo, TypeAnalyzer, TypeMapper};
use crate::backend::c::value::CExpr;
use crate::backend::ir::{CType, FunSig};
use crate::config::GLOBAL_ALLOCATOR_NAME_PREFIX;
use crate::core::syntax::{Name, PrimOp, Term};
use crate::diagnostic::Diagnostic;
use crate::front::parser::TopLevel;
use std::collections::HashMap;
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
                if self.should_emit_zero_arg_getter(body) {
                    return self.emit_zero_arg_getter(name, body);
                }
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

    fn emit_zero_arg_getter(&self, name: &str, body: &Term<'_>) -> Result<String, Diagnostic> {
        let mut ctx = EmitCtx::new();
        let value = self.expr_emitter.emit_expr(
            body,
            &mut ctx,
            self.type_analyzer.enum_map(),
            self.type_analyzer.struct_map(),
        )?;
        let escaped = self.name_resolver.escape(name);
        let cache_flag = format!("_ligare_init_{escaped}");
        let cache_value = format!("_ligare_value_{escaped}");
        let init_stmt = match value.expr {
            CExpr::Match(plan) => {
                let block = self
                    .match_emitter
                    .emit(&plan, 0, self.type_analyzer.enum_map());
                format!(
                    "{}        {cache_value} = {};\n",
                    Self::indent_block(&block, "    "),
                    self.name_resolver.result_temp(0)
                )
            }
            CExpr::Code(code) => format!("        {cache_value} = {};\n", code.as_str()),
        };
        Ok(format!(
            "static int {cache_flag};\nstatic {} {cache_value};\n{} {}(void) {{\n    if (!{cache_flag}) {{\n{init_stmt}        {cache_flag} = 1;\n    }}\n    return {cache_value};\n}}\n",
            value.ctype.c_name(),
            value.ctype.c_name(),
            escaped,
        ))
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
            Term::StructCons(name, values) => {
                self.struct_requires_heap_field(name)
                    || values
                        .iter()
                        .any(|value| self.term_requires_allocation(value))
            }
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
            .is_some_and(|variant| variant.fields.iter().any(|field| field.boxed))
    }

    fn struct_requires_heap_field(&self, sname: &str) -> bool {
        self.type_analyzer
            .struct_map()
            .get(sname)
            .is_some_and(|info| info.fields.iter().any(|field| field.boxed))
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
            if let Some(main_body) = self.runtime_main_body(tops) {
                let mut names = self
                    .name_resolver
                    .collect_called_names(&[main_body], raw_defs);
                names.insert("main".to_string());
                names
            } else {
                self.name_resolver.all_def_names(raw_defs)
            }
        } else {
            self.name_resolver.collect_called_names(outputs, raw_defs)
        };
        let extern_names = self.collect_extern_names(raw_defs);
        let called_extern_names =
            self.collect_called_extern_names(tops, outputs, raw_defs, &called_names, &extern_names);
        let clone_type_names = self.type_analyzer.clone_required_type_names();
        let allocation_required = self.codegen_roots_require_allocation(
            tops,
            raw_defs,
            outputs,
            &called_names,
            &called_extern_names,
            &clone_type_names,
        );
        let allocator = self.resolve_global_allocator(raw_defs, allocation_required)?;
        self.expr_emitter.set_global_allocator(allocator.clone());
        self.expr_emitter.set_extern_names(extern_names.clone());
        self.expr_emitter
            .set_clone_type_names(clone_type_names.clone());
        self.expr_emitter
            .set_zero_arg_getters(self.collect_zero_arg_getters(raw_defs)?);
        if let Some(allocator) = &allocator
            && !allocator.is_default
        {
            called_names.insert(allocator.allocate.clone());
            called_names.insert(allocator.deallocate.clone());
            called_names.insert(allocator.reallocate.clone());
        }
        let filter_top_constants = outputs.is_empty() && self.runtime_main_body(tops).is_some();

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
        if self.extern_clone_helpers_required(&called_extern_names, &clone_type_names) {
            let allocator = allocator.as_ref().ok_or_else(|| {
                Diagnostic::new(
                    "deep-copying extern struct/enum values requires a global allocator",
                )
            })?;
            self.emit_clone_helpers(&mut out, &clone_type_names, allocator);
            out.push('\n');
        }

        for top in tops {
            if let TopLevel::TLDef(name, params, _m_ret, body, _) = top
                && params.is_empty()
                && self.name_resolver.count_lams(body) == 0
                && *name != "main"
                && (!filter_top_constants
                    || called_names.contains(*name)
                    || !self.term_requires_allocation(body))
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
        called_extern_names: &HashSet<String>,
        clone_type_names: &HashSet<String>,
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
                            && (!self.runtime_main_body(tops).is_some() || called_names.contains(*name))
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
            || self.extern_clone_helpers_required(called_extern_names, clone_type_names)
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

    fn collect_zero_arg_getters(
        &self,
        raw_defs: &[TopLevel<'_>],
    ) -> Result<HashMap<String, CType>, Diagnostic> {
        let mut getters = HashMap::new();
        for top in raw_defs {
            let TopLevel::TLDef(name, params, m_ret, body, _) = top else {
                continue;
            };
            if *name == "main"
                || name.starts_with(GLOBAL_ALLOCATOR_NAME_PREFIX)
                || !params.is_empty()
                || self.name_resolver.count_lams(body) != 0
                || !self.should_emit_zero_arg_getter(body)
            {
                continue;
            }
            getters.insert(
                (*name).to_string(),
                self.type_analyzer.def_return_ctype(params, *m_ret, body)?,
            );
        }
        Ok(getters)
    }

    fn should_emit_zero_arg_getter(&self, body: &Term<'_>) -> bool {
        !self.term_is_static_initializer(body)
    }

    fn term_is_static_initializer(&self, term: &Term<'_>) -> bool {
        match self.peel_annotations(term) {
            Term::LitInt(_) | Term::LitBool(_) | Term::LitStr(_) => true,
            Term::StructCons(name, values) => {
                !self.struct_requires_heap_field(name)
                    && values
                        .iter()
                        .all(|value| self.term_is_static_initializer(value))
            }
            Term::Variant(uname, idx, payloads) => {
                !self.variant_requires_heap_payload(uname, *idx)
                    && payloads
                        .iter()
                        .all(|value| self.term_is_static_initializer(value))
            }
            _ => false,
        }
    }

    fn indent_block(block: &str, prefix: &str) -> String {
        block
            .lines()
            .map(|line| {
                let mut out = String::with_capacity(prefix.len() + line.len() + 1);
                out.push_str(prefix);
                out.push_str(line);
                out.push('\n');
                out
            })
            .collect()
    }

    fn collect_extern_names(&self, raw_defs: &[TopLevel<'_>]) -> HashSet<String> {
        raw_defs
            .iter()
            .filter_map(|top| {
                if let TopLevel::TLExternDef(name, ..) = top {
                    Some((*name).to_string())
                } else {
                    None
                }
            })
            .collect()
    }

    fn collect_called_extern_names(
        &self,
        tops: &[TopLevel<'_>],
        outputs: &[&Term<'_>],
        raw_defs: &[TopLevel<'_>],
        called_names: &HashSet<String>,
        extern_names: &HashSet<String>,
    ) -> HashSet<String> {
        let extern_name_refs = extern_names
            .iter()
            .map(String::as_str)
            .collect::<HashSet<_>>();
        let mut called = HashSet::new();
        if let Some(main_body) = self.runtime_main_body(tops) {
            self.name_resolver.collect_matching_names_in_term(
                main_body,
                &extern_name_refs,
                &mut called,
            );
        }
        for term in outputs {
            self.name_resolver
                .collect_matching_names_in_term(term, &extern_name_refs, &mut called);
        }
        for raw_def in raw_defs {
            if let TopLevel::TLDef(name, _, _, body, _) = raw_def
                && called_names.contains(*name)
            {
                self.name_resolver.collect_matching_names_in_term(
                    body,
                    &extern_name_refs,
                    &mut called,
                );
            }
        }
        called
    }

    fn extern_clone_helpers_required(
        &self,
        called_extern_names: &HashSet<String>,
        clone_type_names: &HashSet<String>,
    ) -> bool {
        self.fun_sigs.iter().any(|(name, sig)| {
            called_extern_names.contains(*name)
                && (sig
                    .param_types
                    .iter()
                    .any(|ty| self.ctype_requires_clone(ty, clone_type_names))
                    || self.ctype_requires_clone(&sig.ret_type, clone_type_names))
        })
    }

    fn ctype_requires_clone(&self, ctype: &CType, clone_type_names: &HashSet<String>) -> bool {
        match ctype {
            CType::Enum(name) | CType::Struct(name) => clone_type_names.contains(name),
            _ => false,
        }
    }

    fn emit_clone_helpers(
        &self,
        out: &mut String,
        clone_type_names: &HashSet<String>,
        allocator: &GlobalAllocator,
    ) {
        let mut names = clone_type_names.iter().cloned().collect::<Vec<_>>();
        names.sort();
        for name in &names {
            if self.type_analyzer.struct_map().contains_key(name) {
                let ctype = CType::Struct(name.clone());
                out.push_str(&format!(
                    "static {} {}({} value);\n",
                    ctype.c_name(),
                    ExpressionEmitter::clone_helper_name(&ctype),
                    ctype.c_name()
                ));
            } else if self.type_analyzer.enum_map().contains_key(name) {
                let ctype = CType::Enum(name.clone());
                out.push_str(&format!(
                    "static {} {}({} value);\n",
                    ctype.c_name(),
                    ExpressionEmitter::clone_helper_name(&ctype),
                    ctype.c_name()
                ));
            }
        }
        if !names.is_empty() {
            out.push('\n');
        }
        for name in &names {
            if let Some(info) = self.type_analyzer.struct_map().get(name) {
                out.push_str(&self.emit_struct_clone_helper(
                    name,
                    info,
                    clone_type_names,
                    allocator,
                ));
            } else if let Some(info) = self.type_analyzer.enum_map().get(name) {
                out.push_str(&self.emit_enum_clone_helper(name, info, clone_type_names, allocator));
            }
            out.push('\n');
        }
    }

    fn emit_struct_clone_helper(
        &self,
        name: &str,
        info: &StructInfo,
        clone_type_names: &HashSet<String>,
        allocator: &GlobalAllocator,
    ) -> String {
        let ctype = CType::Struct(name.to_string());
        let ty = ctype.c_name();
        let helper = ExpressionEmitter::clone_helper_name(&ctype);
        let mut out = format!("static {ty} {helper}({ty} value) {{\n    {ty} out = value;\n");
        for (field_idx, field) in info.fields.iter().enumerate() {
            let access = format!("value.{}", field.name);
            let value_expr = self.clone_field_expr(
                &field.logical_type,
                field.boxed,
                &access,
                clone_type_names,
                allocator,
                &format!("{ty}_{field_idx}"),
            );
            if value_expr != access {
                out.push_str(&format!("    out.{} = {};\n", field.name, value_expr));
            }
        }
        out.push_str("    return out;\n}\n");
        out
    }

    fn emit_enum_clone_helper(
        &self,
        name: &str,
        info: &EnumInfo,
        clone_type_names: &HashSet<String>,
        allocator: &GlobalAllocator,
    ) -> String {
        let ctype = CType::Enum(name.to_string());
        let ty = ctype.c_name();
        let helper = ExpressionEmitter::clone_helper_name(&ctype);
        let mut out = format!("static {ty} {helper}({ty} value) {{\n    switch (value.tag) {{\n");
        for (variant_idx, variant) in info.variants.iter().enumerate() {
            if variant.fields.is_empty() {
                out.push_str(&format!("    case {variant_idx}: return value;\n"));
                continue;
            }
            let field_inits = variant
                .fields
                .iter()
                .enumerate()
                .map(|(field_idx, field)| {
                    let access = format!("value.data.{}.{}", variant.name, field.name);
                    let value_expr = self.clone_field_expr(
                        &field.logical_type,
                        field.boxed,
                        &access,
                        clone_type_names,
                        allocator,
                        &format!("{ty}_{variant_idx}_{field_idx}"),
                    );
                    format!(".{} = {}", field.name, value_expr)
                })
                .collect::<Vec<_>>()
                .join(", ");
            out.push_str(&format!(
                "    case {variant_idx}: return (({ty}){{ .tag = {variant_idx}, .data = {{ .{} = {{ {} }} }} }});\n",
                variant.name, field_inits
            ));
        }
        out.push_str("    default: return value;\n    }\n}\n");
        out
    }

    fn clone_field_expr(
        &self,
        logical_type: &CType,
        boxed: bool,
        access: &str,
        clone_type_names: &HashSet<String>,
        allocator: &GlobalAllocator,
        suffix: &str,
    ) -> String {
        if boxed {
            let pointee_ty = logical_type.c_name();
            let helper_value =
                self.clone_value_expr(logical_type, &format!("*({access})"), clone_type_names);
            let ptr_name = format!("_ligare_clone_box_{suffix}");
            return format!(
                "({{ {pointee_ty}* {ptr_name} = NULL; if ({access} != NULL) {{ {ptr_name} = ({pointee_ty}*){}(sizeof({pointee_ty})); *{ptr_name} = {}; }} {ptr_name}; }})",
                allocator.allocate, helper_value
            );
        }
        self.clone_value_expr(logical_type, access, clone_type_names)
    }

    fn clone_value_expr(
        &self,
        ctype: &CType,
        access: &str,
        clone_type_names: &HashSet<String>,
    ) -> String {
        if self.ctype_requires_clone(ctype, clone_type_names) {
            format!("{}({access})", ExpressionEmitter::clone_helper_name(ctype))
        } else {
            access.to_string()
        }
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
