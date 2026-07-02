//! C expression emission.
//!
//! `ExpressionEmitter` translates Ligare `Term` nodes into C expressions.
//! It is a stateless service object — maps are passed at call time for clean
//! ownership semantics.

use crate::backend::c::context::EmitCtx;
use crate::backend::c::emitter::GlobalAllocator;
use crate::backend::c::match_emit::MatchEmitter;
use crate::backend::c::names::NameResolver;
use crate::backend::c::types::{EnumInfo, StructInfo};
use crate::backend::c::value::{CCode, CExpr, CValue, MatchBind, MatchCase, MatchPlan};
use crate::backend::ir::{CType, FunSig};
use crate::config::{BUILTIN_PTR_CAST, BUILTIN_UNIT};
use crate::core::syntax::{MatchBranch, PrimOp, Term};
use crate::diagnostic::Diagnostic;
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

fn c_string_literal(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\000"),
            c if c.is_control() => out.push_str(&format!("\\{:03o}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[derive(Clone, Debug)]
struct CallParts {
    raw_function: Option<String>,
    function: CCode,
    args: Vec<CCode>,
}

struct FieldInit {
    field: String,
    value: CCode,
}

struct TypeNameSets<'a> {
    enums: &'a HashSet<String>,
    structs: &'a HashSet<String>,
}

impl FieldInit {
    fn render(&self) -> String {
        format!(".{} = {}", self.field, self.value.as_str())
    }
}

/// Translates Ligare `Term` nodes into C expressions.
///
/// Stateless service object — holds only function signatures and name resolver.
/// Type maps are passed at call time to avoid self-referential borrows.
pub struct ExpressionEmitter<'a> {
    /// Function signatures for return-type inference.
    fun_sigs: &'a [(&'a str, FunSig)],
    /// Name resolver for escaping.
    names: NameResolver,
    /// Counter for nested match expression temporaries.
    match_expr_counter: Cell<u32>,
    /// Global allocator selected by the C emitter.
    global_allocator: RefCell<Option<GlobalAllocator>>,
    /// Counter for statement-expression temporaries used by allocator expansions.
    allocation_counter: Cell<u32>,
}

impl<'a> ExpressionEmitter<'a> {
    /// Create a new expression emitter.
    pub fn new(fun_sigs: &'a [(&'a str, FunSig)]) -> Self {
        Self {
            fun_sigs,
            names: NameResolver::new(),
            match_expr_counter: Cell::new(1000),
            global_allocator: RefCell::new(None),
            allocation_counter: Cell::new(0),
        }
    }

    pub(crate) fn set_global_allocator(&self, allocator: Option<GlobalAllocator>) {
        *self.global_allocator.borrow_mut() = allocator;
    }

    // ── Main entry ──

    /// Emit a Term as a C expression, returning the emitted code and its C type.
    pub fn emit_expr(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        match term {
            Term::LitInt(n) => Ok(CValue::code(n.to_string(), CType::Int64)),
            Term::LitBool(b) => Ok(CValue::code(if *b { "1" } else { "0" }, CType::Int64)),
            Term::LitStr(s) => Ok(CValue::code(c_string_literal(s), CType::Str)),

            Term::Var(i) => Ok(CValue::code(ctx.name_of(*i)?.to_string(), ctx.type_of(*i)?)),

            Term::Let(name, val, body, _) => {
                let escaped_name = self.names.escape(name);
                let val = self.emit_expr(val, ctx, enum_map, struct_map)?;
                let v = self.value_code(val.clone(), enum_map)?;
                let val_ty = val.ctype;
                let ty_name = val_ty.c_name();
                ctx.push_binding(escaped_name.clone(), val_ty.clone());
                let body = self.emit_expr(body, ctx, enum_map, struct_map)?;
                let b = self.value_code(body.clone(), enum_map)?;
                let body_ty = body.ctype;
                ctx.pop_binding();
                Ok(CValue::code(
                    format!(
                        "({{ {} {} = {}; {}; }})",
                        ty_name,
                        escaped_name,
                        v.as_str(),
                        b.as_str()
                    ),
                    body_ty,
                ))
            }

            Term::Lam(body) => {
                ctx.push_binding(self.names.anon_param(0), CType::Int64);
                let value = self.emit_expr(body, ctx, enum_map, struct_map)?;
                ctx.pop_binding();
                Ok(value)
            }

            Term::IfThenElse(c, t, f) => {
                let cc = self.emit_expr_code(c, ctx, enum_map, struct_map)?;
                let then_value = self.emit_expr(t, ctx, enum_map, struct_map)?;
                let ct = self.value_code(then_value.clone(), enum_map)?;
                let cf = self.emit_expr_code(f, ctx, enum_map, struct_map)?;
                Ok(CValue::code(
                    format!("({}) ? ({}) : ({})", cc.as_str(), ct.as_str(), cf.as_str()),
                    then_value.ctype,
                ))
            }

            Term::App(_, _) => self.emit_app(term, ctx, enum_map, struct_map),

            Term::Annot(inner, _) => self.emit_expr(inner, ctx, enum_map, struct_map),
            Term::Unsafe(inner) => self.emit_expr(inner, ctx, enum_map, struct_map),
            Term::Pure(inner) => self.emit_expr(inner, ctx, enum_map, struct_map),

            Term::Builtin(name) | Term::Global(name) => {
                if *name == BUILTIN_UNIT {
                    return Ok(CValue::code("0", CType::Int64));
                }
                let ty = self
                    .fun_sigs
                    .iter()
                    .find(|(n, _)| *n == *name)
                    .map(|(_, sig)| sig.ret_type.clone())
                    .ok_or_else(|| {
                        Diagnostic::new(format!(
                            "Cannot determine C type for `{name}`; missing function signature"
                        ))
                    })?;
                let code = self
                    .fun_sigs
                    .iter()
                    .find(|(n, _)| *n == *name)
                    .filter(|(_, sig)| sig.param_types.is_empty())
                    .map(|_| format!("{}()", self.names.escape(name)))
                    .unwrap_or_else(|| self.names.escape(name));
                Ok(CValue::code(code, ty))
            }

            Term::EnumDef(..) => Ok(CValue::code(String::new(), CType::Int64)),
            Term::StructDef(..) => Ok(CValue::code(String::new(), CType::Int64)),

            Term::StructCons(sname, field_values) => {
                self.emit_struct_cons(sname, field_values, ctx, enum_map, struct_map)
            }
            Term::StructProj(subject, idx) => {
                self.emit_struct_proj(subject, *idx, ctx, enum_map, struct_map)
            }
            Term::Variant(uname, idx, payloads) => {
                self.emit_variant(uname, *idx, payloads, ctx, enum_map, struct_map)
            }
            Term::Match(_scrut, branches) => {
                self.emit_match(_scrut, branches, ctx, enum_map, struct_map)
            }

            _ => Err(Diagnostic::new(format!(
                "emit_expr: unrecognized term {:?}",
                term
            ))),
        }
    }

    fn emit_expr_code(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CCode, Diagnostic> {
        let value = self.emit_expr(term, ctx, enum_map, struct_map)?;
        self.value_code(value, enum_map)
    }

    fn value_code(
        &self,
        value: CValue,
        enum_map: &HashMap<String, EnumInfo>,
    ) -> Result<CCode, Diagnostic> {
        match value.expr {
            CExpr::Code(code) => Ok(code),
            CExpr::Match(plan) => {
                let counter = self.match_expr_counter.get();
                self.match_expr_counter.set(counter + 1);
                Ok(CCode::new(
                    MatchEmitter::new().emit_expr(&plan, counter, enum_map),
                ))
            }
        }
    }

    // ── Sub-emitters ──

    fn emit_struct_cons(
        &self,
        sname: &str,
        field_values: &[&Term<'_>],
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let type_name: String = sname.to_string();
        let Some(info) = struct_map.get(&type_name) else {
            return Err(Diagnostic::new(format!(
                "Cannot emit constructor for unknown struct `{type_name}`"
            )));
        };
        if field_values.len() != info.fields.len() {
            return Err(Diagnostic::new(format!(
                "Struct `{type_name}` expects {} field(s), got {}",
                info.fields.len(),
                field_values.len()
            )));
        }
        let field_codes: Vec<CCode> = field_values
            .iter()
            .map(|v| self.emit_expr_code(v, ctx, enum_map, struct_map))
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let field_codes = field_codes
            .iter()
            .map(CCode::as_str)
            .collect::<Vec<_>>()
            .join(", ");
        Ok(CValue::code(
            format!("(({}){{ {} }})", type_name, field_codes),
            CType::Struct(type_name),
        ))
    }

    fn emit_struct_proj(
        &self,
        subject: &Term<'_>,
        idx: usize,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let subject = self.emit_expr(subject, ctx, enum_map, struct_map)?;
        let scode = self.value_code(subject.clone(), enum_map)?;
        let sty = subject.ctype;
        if let CType::Struct(ref sname) = sty
            && let Some(info) = struct_map.get(sname)
            && let Some((fname, ftype)) = info.fields.get(idx)
        {
            return Ok(CValue::code(
                format!("({}).{}", scode.as_str(), fname),
                ftype.clone(),
            ));
        }
        Err(Diagnostic::new(format!(
            "Cannot determine C type for struct projection field {idx} on {:?}",
            sty
        )))
    }

    fn emit_variant(
        &self,
        uname: &str,
        idx: usize,
        payloads: &[&Term<'_>],
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let type_name: String = uname.to_string();
        let data_init =
            self.variant_data_init(&type_name, idx, payloads, ctx, enum_map, struct_map)?;
        Ok(CValue::code(
            format!(
                "(({}){{ .tag = {}, .data = {} }})",
                type_name, idx, data_init
            ),
            CType::Enum(type_name),
        ))
    }

    fn variant_data_init(
        &self,
        type_name: &str,
        idx: usize,
        payloads: &[&Term<'_>],
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<String, Diagnostic> {
        let info = enum_map.get(type_name).ok_or_else(|| {
            Diagnostic::new(format!(
                "Cannot emit variant {idx} for unknown enum `{type_name}`"
            ))
        })?;
        let vi = info.variants.get(idx).ok_or_else(|| {
            Diagnostic::new(format!(
                "Cannot emit variant {idx} for enum `{type_name}` with {} variant(s)",
                info.variants.len()
            ))
        })?;
        if payloads.len() != vi.fields.len() {
            return Err(Diagnostic::new(format!(
                "Variant `{}.{}` expects {} payload(s), got {}",
                type_name,
                vi.name,
                vi.fields.len(),
                payloads.len()
            )));
        }
        if vi.fields.is_empty() {
            return Ok(format!("{{ .{} = {{0}} }}", vi.name));
        }
        let field_inits: Vec<FieldInit> = vi
            .fields
            .iter()
            .zip(payloads.iter())
            .map(|((fnm, fty), p)| {
                let value = self.emit_expr(p, ctx, enum_map, struct_map)?;
                let code = self.value_code(value.clone(), enum_map)?;
                let recursive_payload_ty = Self::recursive_payload_storage_type(fty, type_name);
                let code = if let Some(payload_ty) = recursive_payload_ty.as_ref() {
                    self.emit_heap_copy(payload_ty, code.as_str())?
                } else {
                    code
                };
                Ok(FieldInit {
                    field: fnm.clone(),
                    value: code,
                })
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        let field_inits = field_inits
            .iter()
            .map(FieldInit::render)
            .collect::<Vec<_>>()
            .join(", ");
        Ok(format!("{{ .{} = {{ {} }} }}", vi.name, field_inits))
    }

    fn emit_match(
        &self,
        scrut: &Term<'_>,
        branches: &[MatchBranch<'_>],
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let scrut_value = self.emit_expr(scrut, ctx, enum_map, struct_map)?;
        let sc = self.value_code(scrut_value.clone(), enum_map)?;
        let sc_ty = scrut_value.ctype;
        let scrut_enum = match &sc_ty {
            CType::Enum(name) => Some(name.as_str()),
            _ => None,
        };
        let mut cases = Vec::new();
        let mut ret_ty: Option<CType> = None;
        let enum_names: HashSet<String> = enum_map.keys().cloned().collect();
        let struct_names: HashSet<String> = struct_map.keys().cloned().collect();
        let type_names = TypeNameSets {
            enums: &enum_names,
            structs: &struct_names,
        };
        for (idx, binds, body) in branches.iter() {
            let mut branch_ctx = ctx.snapshot();
            for (bind_idx, (name, ty)) in binds.iter().enumerate().rev() {
                let cty =
                    self.match_bind_ctype(scrut_enum, *idx, bind_idx, ty, enum_map, &type_names)?;
                branch_ctx.push_binding(self.names.escape(name), cty);
            }
            let body_value = self.emit_expr(body, &mut branch_ctx, enum_map, struct_map)?;
            let bc = self.value_code(body_value.clone(), enum_map)?;
            if let Some(prev_ty) = &ret_ty {
                if prev_ty != &body_value.ctype {
                    return Err(Diagnostic::new(format!(
                        "Match branches return incompatible C types: {} and {}",
                        prev_ty.c_name(),
                        body_value.ctype.c_name()
                    )));
                }
            } else {
                ret_ty = Some(body_value.ctype.clone());
            }
            let mut case_binds = Vec::new();
            for (bind_idx, (_name, ty)) in binds.iter().enumerate() {
                let cty =
                    self.match_bind_ctype(scrut_enum, *idx, bind_idx, ty, enum_map, &type_names)?;
                case_binds.push(MatchBind {
                    name: self.names.escape(_name),
                    ctype: cty,
                });
            }
            cases.push(MatchCase {
                variant_idx: *idx,
                binds: case_binds,
                body_code: bc,
            });
        }
        let ret_ty = ret_ty.ok_or_else(|| {
            Diagnostic::new("Cannot determine C type for match expression without branches")
        })?;
        Ok(CValue::match_(MatchPlan {
            scrut_type: sc_ty,
            scrut_code: sc,
            ret_type: ret_ty.clone(),
            cases,
        }))
    }

    fn match_bind_ctype(
        &self,
        scrut_enum: Option<&str>,
        variant_idx: usize,
        bind_idx: usize,
        fallback_ty: &Term<'_>,
        enum_map: &HashMap<String, EnumInfo>,
        type_names: &TypeNameSets<'_>,
    ) -> Result<CType, Diagnostic> {
        if let Some(uname) = scrut_enum
            && let Some(info) = enum_map.get(uname)
            && let Some(variant) = info.variants.get(variant_idx)
            && let Some((_, cty)) = variant.fields.get(bind_idx)
        {
            if let CType::Ptr(inner) = cty
                && matches!(inner.as_ref(), CType::Enum(inner_name) if inner_name == uname)
            {
                return Ok((**inner).clone());
            }
            return Ok(cty.clone());
        }
        crate::backend::ir::constraint_to_ctype(fallback_ty, type_names.enums, type_names.structs)
    }

    fn recursive_payload_storage_type(fty: &CType, type_name: &str) -> Option<CType> {
        if let CType::Ptr(inner) = fty
            && matches!(inner.as_ref(), CType::Enum(inner_name) if inner_name == type_name)
        {
            return Some((**inner).clone());
        }
        None
    }

    // ── Function call emission ──

    pub fn emit_app(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let Term::App(f, a) = term else {
            unreachable!()
        };
        if let Term::App(prim, left) = *f
            && let Term::PrimOp(op) = *prim
        {
            let left = self.emit_expr(left, ctx, enum_map, struct_map)?;
            let right = self.emit_expr(a, ctx, enum_map, struct_map)?;
            if *op == PrimOp::Add && left.ctype == CType::Str && right.ctype == CType::Str {
                let left_code = self.value_code(left, enum_map)?;
                let right_code = self.value_code(right, enum_map)?;
                return Ok(CValue::code(
                    self.emit_string_concat(left_code.as_str(), right_code.as_str())?,
                    CType::Str,
                ));
            }
            let left_code = self.value_code(left, enum_map)?;
            let right_code = self.value_code(right, enum_map)?;
            return Ok(CValue::code(
                self.emit_binop(*op, left_code.as_str(), right_code.as_str()),
                CType::Int64,
            ));
        }
        if matches!(*f, Term::PrimOp(_)) {
            return self.emit_expr(a, ctx, enum_map, struct_map);
        }
        if let Some((target, pointer)) = Self::ptr_cast_parts(term) {
            return self.emit_ptr_cast(target, pointer, ctx, enum_map, struct_map);
        }
        let call = self.collect_call_args(term, ctx, enum_map, struct_map)?;
        let param_count = self
            .fun_sigs
            .iter()
            .find(|(n, _)| Some(*n) == call.raw_function.as_deref())
            .map(|(_, sig)| sig.param_types.len())
            .ok_or_else(|| {
                Diagnostic::new(format!(
                    "Cannot emit call to `{}`; missing function signature",
                    call.function.as_str()
                ))
            })?;
        let args = if call.args.len() > param_count {
            call.args[call.args.len() - param_count..].to_vec()
        } else {
            call.args
        };
        let ret_ty = self
            .fun_sigs
            .iter()
            .find(|(n, _)| Some(*n) == call.raw_function.as_deref())
            .map(|(_, sig)| sig.ret_type.clone())
            .ok_or_else(|| {
                Diagnostic::new(format!(
                    "Cannot determine C return type for `{}`; missing function signature",
                    call.function.as_str()
                ))
            })?;
        let args = args
            .iter()
            .map(CCode::as_str)
            .collect::<Vec<_>>()
            .join(", ");
        Ok(CValue::code(
            format!("{}({})", call.function.as_str(), args),
            ret_ty,
        ))
    }

    fn ptr_cast_parts<'term>(
        term: &'term Term<'term>,
    ) -> Option<(&'term Term<'term>, &'term Term<'term>)> {
        let Term::App(f, pointer) = term else {
            return None;
        };
        let Term::App(head, target) = *f else {
            return None;
        };
        if matches!(*head, Term::Builtin(name) | Term::Global(name) if *name == BUILTIN_PTR_CAST) {
            Some((target, pointer))
        } else {
            None
        }
    }

    fn emit_ptr_cast(
        &self,
        target: &Term<'_>,
        pointer: &Term<'_>,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CValue, Diagnostic> {
        let pointer = self.emit_expr(pointer, ctx, enum_map, struct_map)?;
        let pointer_code = self.value_code(pointer, enum_map)?;
        let enum_names: HashSet<String> = enum_map.keys().cloned().collect();
        let struct_names: HashSet<String> = struct_map.keys().cloned().collect();
        let target_ty = CType::Ptr(Box::new(crate::backend::ir::constraint_to_ctype(
            target,
            &enum_names,
            &struct_names,
        )?));
        Ok(CValue::code(
            format!("(({}){})", target_ty.c_name(), pointer_code.as_str()),
            target_ty,
        ))
    }

    fn collect_call_args(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        enum_map: &HashMap<String, EnumInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<CallParts, Diagnostic> {
        match term {
            Term::App(f, a) => {
                let mut call = self.collect_call_args(f, ctx, enum_map, struct_map)?;
                let arg = self.emit_expr(a, ctx, enum_map, struct_map)?;
                call.args.push(self.value_code(arg, enum_map)?);
                Ok(call)
            }
            _ => {
                let raw_function = match term {
                    Term::Builtin(name) | Term::Global(name) => Some((*name).to_string()),
                    Term::Annot(inner, _) => match inner {
                        Term::Builtin(name) | Term::Global(name) => Some((*name).to_string()),
                        _ => None,
                    },
                    _ => None,
                };
                let value = self.emit_expr(term, ctx, enum_map, struct_map)?;
                Ok(CallParts {
                    raw_function,
                    function: self.value_code(value, enum_map)?,
                    args: Vec::new(),
                })
            }
        }
    }

    /// Emit a binary operator as a C expression.
    pub fn emit_binop(&self, op: PrimOp, left: &str, right: &str) -> String {
        match op {
            PrimOp::Add => format!("({left} + {right})"),
            PrimOp::Sub => format!("({left} - {right})"),
            PrimOp::Mul => format!("({left} * {right})"),
            PrimOp::Div => format!("({left} / {right})"),
            PrimOp::Mod_ => format!("({left} % {right})"),
            PrimOp::Eq => format!("({left} == {right})"),
            PrimOp::Neq => format!("({left} != {right})"),
            PrimOp::Lt => format!("({left} < {right})"),
            PrimOp::Gt => format!("({left} > {right})"),
            PrimOp::Le => format!("({left} <= {right})"),
            PrimOp::Ge => format!("({left} >= {right})"),
        }
    }

    fn emit_string_concat(&self, left: &str, right: &str) -> Result<String, Diagnostic> {
        let allocator =
            self.global_allocator.borrow().clone().ok_or_else(|| {
                Diagnostic::new("string concatenation requires a global allocator")
            })?;
        let id = self.allocation_counter.get();
        self.allocation_counter.set(id + 1);
        let l = format!("_ligare_l{id}");
        let r = format!("_ligare_r{id}");
        let ln = format!("_ligare_ln{id}");
        let rn = format!("_ligare_rn{id}");
        let i = format!("_ligare_i{id}");
        let out = format!("_ligare_out{id}");
        Ok(format!(
            "({{ const char* {l} = ({left}); const char* {r} = ({right}); size_t {ln} = 0; while ({l}[{ln}] != '\\0') {{ {ln}++; }} size_t {rn} = 0; while ({r}[{rn}] != '\\0') {{ {rn}++; }} char* {out} = (char*){}({ln} + {rn} + 1); size_t {i} = 0; for (; {i} < {ln}; {i}++) {{ {out}[{i}] = {l}[{i}]; }} for (size_t _ligare_j{id} = 0; _ligare_j{id} < {rn}; _ligare_j{id}++) {{ {out}[{ln} + _ligare_j{id}] = {r}[_ligare_j{id}]; }} {out}[{ln} + {rn}] = '\\0'; {out}; }})",
            allocator.allocate
        ))
    }

    fn emit_heap_copy(&self, ctype: &CType, value: &str) -> Result<CCode, Diagnostic> {
        let allocator = self.global_allocator.borrow().clone().ok_or_else(|| {
            Diagnostic::new("recursive enum construction requires a global allocator")
        })?;
        let id = self.allocation_counter.get();
        self.allocation_counter.set(id + 1);
        let ty = ctype.c_name();
        let ptr = format!("_ligare_heap{id}");
        Ok(CCode::new(format!(
            "({{ {ty}* {ptr} = ({ty}*){}(sizeof({ty})); *{ptr} = ({value}); {ptr}; }})",
            allocator.allocate
        )))
    }
}
