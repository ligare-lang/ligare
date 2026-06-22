//! Minimal IR types for C code generation.
//!
//! `CType` maps term-level data to C declarations.
//! `FunSig` records the erased C types of function parameters and return
//! values, populated during erasure and consumed by the C backend.

use std::collections::HashSet;

/// Concrete C type — only the data-relevant ones.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CType {
    Int64,
    Str,
    /// Named union type (for tagged unions)
    Union(String),
}

impl CType {
    pub fn c_name(&self) -> String {
        match self {
            CType::Int64 => "int64_t".into(),
            CType::Str => "const char*".into(),
            CType::Union(name) => name.clone(),
        }
    }
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
        params: &[(
            crate::core::syntax::Name<'_>,
            Option<&crate::core::syntax::Term<'_>>,
        )],
        m_ret: Option<&crate::core::syntax::Term<'_>>,
        body: &crate::core::syntax::Term<'_>,
        union_names: &HashSet<String>,
    ) -> Result<Self, String> {
        let param_types: Vec<CType> = params
            .iter()
            .map(|(_, mc)| mc.map_or(Ok(CType::Int64), |c| constraint_to_ctype(c, union_names)))
            .collect::<Result<Vec<_>, _>>()?;
        let ret_type = match m_ret {
            Some(t) => constraint_to_ctype(t, union_names)?,
            None => infer_ret_ctype(body, &param_types),
        };
        Ok(FunSig {
            param_types,
            ret_type,
        })
    }
}

/// Infer the C return type from a term body, given the parameter C types
/// (in declaration order, i.e. left-to-right).  This mirrors the type
/// inference that `emit_fun` does during code generation.
fn infer_ret_ctype(body: &crate::core::syntax::Term<'_>, param_types: &[CType]) -> CType {
    match body {
        crate::core::syntax::Term::Var(i) => param_types.get(*i).cloned().unwrap_or(CType::Int64),
        crate::core::syntax::Term::LitStr(_) => CType::Str,
        crate::core::syntax::Term::Lam(inner) => {
            // Lambda wrapping: the inner body determines the return type.
            // Push a dummy Int64 for the lambda parameter and recurse.
            let mut extended: Vec<CType> = vec![CType::Int64];
            extended.extend_from_slice(param_types);
            infer_ret_ctype(inner, &extended)
        }
        _ => CType::Int64,
    }
}

/// Map a constraint Term to its C type.  Recognizes builtin type names
/// and user-defined union types; returns an error for unrecognized types.
pub fn constraint_to_ctype(
    t: &crate::core::syntax::Term<'_>,
    union_names: &HashSet<String>,
) -> Result<CType, String> {
    match t {
        crate::core::syntax::Term::Builtin(name) if *name == "str" => Ok(CType::Str),
        crate::core::syntax::Term::Builtin(name) if union_names.contains(&name.to_string()) => {
            Ok(CType::Union(name.to_string()))
        }
        crate::core::syntax::Term::Builtin(_)
        | crate::core::syntax::Term::LitInt(_)
        | crate::core::syntax::Term::LitBool(_)
        | crate::core::syntax::Term::Var(_)
        | crate::core::syntax::Term::Universe(_) => Ok(CType::Int64),
        _ => Err(format!("Cannot map constraint {:?} to C type", t)),
    }
}
