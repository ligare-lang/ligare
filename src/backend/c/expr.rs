//! C expression emission.
//!
//! `ExpressionEmitter` translates Ligare `Term` nodes into C expressions.
//! It is a stateless service object — maps are passed at call time for clean
//! ownership semantics.

mod aggregates;
mod calls;

use crate::backend::c::context::EmitCtx;
use crate::backend::c::emitter::GlobalAllocator;
use crate::backend::c::match_emit::MatchEmitter;
use crate::backend::c::names::NameResolver;
use crate::backend::c::types::{EnumInfo, StructInfo};
use crate::backend::c::value::{CCode, CExpr, CValue, MatchBind, MatchCase, MatchPlan};
use crate::backend::ir::{CType, FunSig};
use crate::config::{BUILTIN_PTR_CAST, BUILTIN_UNIT, is_builtin_name};
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
    /// External C function names.
    extern_names: RefCell<HashSet<String>>,
    /// Named struct/enum types that require deep-clone helpers at unsafe boundaries.
    clone_type_names: RefCell<HashSet<String>>,
    /// Zero-arg top-level defs emitted as runtime getter functions.
    zero_arg_getters: RefCell<HashMap<String, CType>>,
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
            extern_names: RefCell::new(HashSet::new()),
            clone_type_names: RefCell::new(HashSet::new()),
            zero_arg_getters: RefCell::new(HashMap::new()),
            allocation_counter: Cell::new(0),
        }
    }

    pub(crate) fn set_global_allocator(&self, allocator: Option<GlobalAllocator>) {
        *self.global_allocator.borrow_mut() = allocator;
    }

    pub(crate) fn set_zero_arg_getters(&self, getters: HashMap<String, CType>) {
        *self.zero_arg_getters.borrow_mut() = getters;
    }

    pub(crate) fn set_extern_names(&self, extern_names: HashSet<String>) {
        *self.extern_names.borrow_mut() = extern_names;
    }

    pub(crate) fn set_clone_type_names(&self, clone_type_names: HashSet<String>) {
        *self.clone_type_names.borrow_mut() = clone_type_names;
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
                if is_builtin_name(name, BUILTIN_UNIT) {
                    return Ok(CValue::code("0", CType::Int64));
                }
                if let Some(ret_ty) = self.zero_arg_getters.borrow().get(*name).cloned() {
                    return Ok(CValue::code(
                        format!("{}()", self.names.escape(name)),
                        ret_ty,
                    ));
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

    fn ctype_requires_clone(&self, ctype: &CType) -> bool {
        match ctype {
            CType::Enum(name) | CType::Struct(name) => {
                self.clone_type_names.borrow().contains(name)
            }
            _ => false,
        }
    }

    fn clone_value_expr(&self, ctype: &CType, value: &str) -> Result<String, Diagnostic> {
        match ctype {
            CType::Enum(_) | CType::Struct(_) if self.ctype_requires_clone(ctype) => {
                Ok(format!("{}({value})", Self::clone_helper_name(ctype)))
            }
            _ => Ok(value.to_string()),
        }
    }

    pub(crate) fn clone_helper_name(ctype: &CType) -> String {
        format!("ligare_clone_{}", ctype.c_name())
    }
}
