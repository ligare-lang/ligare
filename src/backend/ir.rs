//! Minimal IR types for C code generation.
//!
//! `CType` maps term-level data to C declarations.
//! `FunSig` records the erased C types of function parameters and return
//! values, populated during erasure and consumed by the C backend.

use std::collections::HashSet;

use crate::checker::builtin::BuiltinRegistry;
use crate::config::{
    BUILTIN_BOOL, BUILTIN_C_INT, BUILTIN_C_UINT, BUILTIN_I8, BUILTIN_I16, BUILTIN_I32, BUILTIN_I64,
    BUILTIN_INT, BUILTIN_IO, BUILTIN_PTR, BUILTIN_STR, BUILTIN_U8, BUILTIN_U16, BUILTIN_U32,
    BUILTIN_U64, BUILTIN_UNIT, canonical_builtin_name, is_builtin_name,
};
use crate::core::semantics::SemanticQueries;
use crate::core::syntax::Term;
use crate::diagnostic::Diagnostic;

/// Concrete C type — only the data-relevant ones.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CType {
    Int64,
    Int8,
    Int16,
    Int32,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    CInt,
    CUInt,
    Str,
    Ptr(Box<CType>),
    /// Named enum type (compiled as a tagged C representation)
    Enum(String),
    /// Named struct type (for product types)
    Struct(String),
}

impl CType {
    pub fn c_name(&self) -> String {
        match self {
            CType::Int64 => "int64_t".into(),
            CType::Int8 => "int8_t".into(),
            CType::Int16 => "int16_t".into(),
            CType::Int32 => "int32_t".into(),
            CType::UInt8 => "uint8_t".into(),
            CType::UInt16 => "uint16_t".into(),
            CType::UInt32 => "uint32_t".into(),
            CType::UInt64 => "uint64_t".into(),
            CType::CInt => "int".into(),
            CType::CUInt => "unsigned int".into(),
            CType::Str => "const char*".into(),
            CType::Ptr(inner) => format!("{}*", inner.c_name()),
            CType::Enum(name) | CType::Struct(name) => c_identifier(name),
        }
    }

    pub fn c_default_value(&self) -> String {
        match self {
            CType::Int64
            | CType::Int8
            | CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::UInt64
            | CType::CInt
            | CType::CUInt => "0".into(),
            CType::Str | CType::Ptr(_) => "NULL".into(),
            CType::Enum(name) | CType::Struct(name) => format!("({}){{0}}", c_identifier(name)),
        }
    }
}

fn c_identifier(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    if out.as_bytes().first().is_some_and(|b| b.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

/// Erased C signature of a named function.
///
/// Parameter constraints like `: int` / `: str` are stripped during
/// erasure, but we capture their C types here so the C backend can emit
/// correct parameter declarations.
#[derive(Debug, Clone)]
pub struct FunSig {
    pub param_types: Vec<CType>,
    pub ret_type: CType,
}

impl FunSig {
    pub fn from_func(
        params: &[(crate::core::syntax::Name<'_>, Option<&Term<'_>>)],
        m_ret: Option<&Term<'_>>,
        body: &Term<'_>,
        enum_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<Self, Diagnostic> {
        // Filter out erased generic parameters constrained by meta-constraints
        // (prop, theorem, proof).
        let data_params: Vec<_> = params
            .iter()
            .filter(|(_, mc)| !mc.is_some_and(|c| is_erased_parameter_constraint(c)))
            .collect();
        let param_types: Vec<CType> = data_params
            .iter()
            .map(|(name, mc)| {
                let Some(c) = mc else {
                    return Err(Diagnostic::new(format!(
                        "Cannot infer C type for parameter `{name}` without an explicit constraint"
                    )));
                };
                constraint_to_ctype(c, enum_names, struct_names)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ret_body = peel_lams(body, params.len());
        let ret_type = match m_ret {
            Some(t) if !is_meta_constraint(t) => constraint_to_ctype(t, enum_names, struct_names)?,
            _ => infer_ret_ctype(ret_body, &param_types, enum_names, struct_names)?,
        };
        Ok(FunSig {
            param_types,
            ret_type,
        })
    }

    pub fn from_extern(
        params: &[(crate::core::syntax::Name<'_>, Option<&Term<'_>>)],
        ret: &Term<'_>,
        enum_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<Self, Diagnostic> {
        let param_types: Vec<CType> = params
            .iter()
            .map(|(name, mc)| {
                let Some(c) = mc else {
                    return Err(Diagnostic::new(format!(
                        "Cannot infer C type for extern parameter `{name}` without an explicit constraint"
                    )));
                };
                constraint_to_ctype(c, enum_names, struct_names)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ret_type = constraint_to_ctype(ret, enum_names, struct_names)?;
        Ok(FunSig {
            param_types,
            ret_type,
        })
    }
}

/// Infer the C return type from a term body, given the parameter C types
/// (in declaration order, i.e. left-to-right).  This mirrors the type
/// inference that `emit_fun` does during code generation.
fn infer_ret_ctype(
    body: &Term<'_>,
    param_types: &[CType],
    enum_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> Result<CType, Diagnostic> {
    match body {
        Term::Var(i) => param_types.get(*i).cloned().ok_or_else(|| {
            Diagnostic::new(format!(
                "Cannot infer C return type: variable index {i} has no parameter type"
            ))
        }),
        Term::LitInt(_) | Term::LitBool(_) => Ok(CType::Int64),
        Term::LitStr(_) => Ok(CType::Str),
        Term::Annot(inner, c) => constraint_to_ctype(c, enum_names, struct_names)
            .or_else(|_| infer_ret_ctype(inner, param_types, enum_names, struct_names)),
        Term::Unsafe(inner) => infer_ret_ctype(inner, param_types, enum_names, struct_names),
        Term::Pure(inner) => infer_ret_ctype(inner, param_types, enum_names, struct_names),
        Term::App(f, _) if is_primop_app(f) => {
            infer_primop_ret_ctype(body).unwrap_or(Ok(CType::Int64))
        }
        Term::IfThenElse(_, then_term, else_term) => {
            let then_ty = infer_ret_ctype(then_term, param_types, enum_names, struct_names)?;
            let else_ty = infer_ret_ctype(else_term, param_types, enum_names, struct_names)?;
            if then_ty == else_ty {
                Ok(then_ty)
            } else {
                Err(Diagnostic::new(format!(
                    "Cannot infer C return type for if expression with branch types {:?} and {:?}",
                    then_ty, else_ty
                )))
            }
        }
        Term::Let(_, _, body, _) | Term::Lam(body) => {
            infer_ret_ctype(body, param_types, enum_names, struct_names)
        }
        Term::Named(_) | Term::NamedLam(..) | Term::NamedMatch(..) | Term::MethodCall(..) => Err(
            Diagnostic::new("parser-level term reached C signature inference before desugaring"),
        ),
        _ => Err(Diagnostic::new(format!(
            "Cannot infer C return type for unannotated body {:?}; add an explicit return type",
            body
        ))),
    }
}

fn peel_lams<'a>(body: &'a Term<'a>, count: usize) -> &'a Term<'a> {
    let mut term = body;
    let mut remaining = count;
    while remaining > 0 {
        match term {
            Term::Annot(inner, _) => term = inner,
            Term::Lam(inner) | Term::NamedLam(_, inner) => {
                term = inner;
                remaining -= 1;
            }
            _ => break,
        }
    }
    term
}

fn is_primop_app(term: &Term<'_>) -> bool {
    match term {
        Term::PrimOp(_) => true,
        Term::App(f, _) => is_primop_app(f),
        _ => false,
    }
}

fn infer_primop_ret_ctype(term: &Term<'_>) -> Option<Result<CType, Diagnostic>> {
    let Term::App(f, right) = term else {
        return None;
    };
    let Term::App(prim, left) = *f else {
        return None;
    };
    let Term::PrimOp(op) = *prim else {
        return None;
    };
    if *op == crate::core::syntax::PrimOp::Add && term_is_str_like(left) && term_is_str_like(right)
    {
        return Some(Ok(CType::Str));
    }
    Some(Ok(CType::Int64))
}

fn term_is_str_like(term: &Term<'_>) -> bool {
    match term {
        Term::LitStr(_) => true,
        Term::Annot(_, constraint) => {
            matches!(**constraint, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_STR))
        }
        Term::Unsafe(inner) | Term::Pure(inner) => term_is_str_like(inner),
        Term::App(_, _) => infer_primop_ret_ctype(term)
            .is_some_and(|result| result.is_ok_and(|ty| ty == CType::Str)),
        _ => false,
    }
}

/// Returns true for Ligare meta-constraints (`data`, `prop`, `theorem`, `proof`).
pub fn is_meta_constraint(t: &Term<'_>) -> bool {
    let builtins = BuiltinRegistry::new();
    SemanticQueries::new(&builtins).is_meta_constraint(t)
}

/// Returns true for generic parameters erased before C code generation.
pub fn is_erased_parameter_constraint(t: &Term<'_>) -> bool {
    let builtins = BuiltinRegistry::new();
    SemanticQueries::new(&builtins).is_erased_parameter_constraint(t)
}

/// Map a constraint Term to its C type.  Recognizes builtin type names,
/// user-defined struct types, and enum types;
/// returns an error for unrecognized types.
pub fn constraint_to_ctype(
    t: &Term<'_>,
    enum_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> Result<CType, Diagnostic> {
    match t {
        Term::Builtin(name) | Term::Global(name)
            if matches!(
                canonical_builtin_name(name),
                BUILTIN_INT | BUILTIN_I64 | BUILTIN_BOOL | BUILTIN_UNIT
            ) =>
        {
            Ok(CType::Int64)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_I8) => {
            Ok(CType::Int8)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_I16) => {
            Ok(CType::Int16)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_I32) => {
            Ok(CType::Int32)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_U8) => {
            Ok(CType::UInt8)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_U16) => {
            Ok(CType::UInt16)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_U32) => {
            Ok(CType::UInt32)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_U64) => {
            Ok(CType::UInt64)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_C_INT) => {
            Ok(CType::CInt)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_C_UINT) => {
            Ok(CType::CUInt)
        }
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_STR) => {
            Ok(CType::Str)
        }
        Term::Builtin(name) | Term::Global(name) if struct_names.contains(&name.to_string()) => {
            Ok(CType::Struct(name.to_string()))
        }
        Term::Builtin(name) | Term::Global(name) if enum_names.contains(&name.to_string()) => {
            Ok(CType::Enum(name.to_string()))
        }
        Term::Builtin(name) | Term::Global(name) => Err(Diagnostic::new(format!(
            "Cannot map unresolved constraint `{name}` to a C type"
        ))),
        Term::Refine(_, parent, _) => constraint_to_ctype(parent, enum_names, struct_names),
        Term::Annot(_, c) => constraint_to_ctype(c, enum_names, struct_names),
        // Handle monomorphized generic type applications like
        // `Option int` → Enum("Option__int") when that instance exists.
        Term::App(head, _) => {
            if matches!(head, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_PTR))
            {
                let (_, args) = collect_type_app(t);
                let [inner] = args.as_slice() else {
                    return Err(Diagnostic::new(format!(
                        "`{BUILTIN_PTR}` expects exactly one type argument"
                    )));
                };
                return Ok(CType::Ptr(Box::new(constraint_to_ctype(
                    inner,
                    enum_names,
                    struct_names,
                )?)));
            }
            if let Term::App(io_head, inner) = t
                && matches!(io_head, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_IO))
            {
                return constraint_to_ctype(inner, enum_names, struct_names);
            }
            if let Term::Builtin(name) | Term::Global(name) = *head
                && is_builtin_name(name, BUILTIN_IO)
            {
                return Ok(CType::Int64);
            }
            if let Some(name) = type_app_name(t) {
                if enum_names.contains(&name) {
                    return Ok(CType::Enum(name));
                }
                if struct_names.contains(&name) {
                    return Ok(CType::Struct(name));
                }
            }
            if let Term::Builtin(name) | Term::Global(name) = *head {
                if enum_names.contains(&name.to_string()) {
                    return Ok(CType::Enum(name.to_string()));
                }
                if struct_names.contains(&name.to_string()) {
                    return Ok(CType::Struct(name.to_string()));
                }
            }
            Err(Diagnostic::new(format!(
                "Cannot map type application {:?} to a C type",
                t
            )))
        }
        _ => Err(Diagnostic::new(format!(
            "Cannot map constraint {:?} to C type",
            t
        ))),
    }
}

fn type_app_name(t: &Term<'_>) -> Option<String> {
    let (head, args) = collect_type_app(t);
    if args.is_empty() {
        return None;
    }
    let (Term::Builtin(base) | Term::Global(base)) = head else {
        return None;
    };
    Some(format!(
        "{}__{}",
        sanitize_type_name(base),
        args.iter()
            .map(|arg| type_arg_slug(arg))
            .collect::<Vec<_>>()
            .join("__")
    ))
}

fn collect_type_app<'a>(t: &'a Term<'a>) -> (&'a Term<'a>, Vec<&'a Term<'a>>) {
    let mut args = Vec::new();
    let mut cur = t;
    while let Term::App(f, a) = cur {
        args.push(*a);
        cur = f;
    }
    args.reverse();
    (cur, args)
}

fn type_arg_slug(t: &Term<'_>) -> String {
    match t {
        Term::Builtin(n) | Term::Global(n) => sanitize_type_name(n),
        Term::App(_, _) => type_app_name(t).unwrap_or_else(|| "unknown".into()),
        _ => "unknown".into(),
    }
}

fn sanitize_type_name(name: &str) -> String {
    name.replace(|c: char| !c.is_ascii_alphanumeric(), "_")
}
