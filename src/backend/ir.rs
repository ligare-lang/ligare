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
    /// Named struct type (for product types)
    Struct(String),
}

impl CType {
    pub fn c_name(&self) -> String {
        match self {
            CType::Int64 => "int64_t".into(),
            CType::Str => "const char*".into(),
            CType::Union(name) => name.clone(),
            CType::Struct(name) => name.clone(),
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
        struct_names: &HashSet<String>,
    ) -> Result<Self, String> {
        // Filter out type-level (generic) parameters — those constrained
        // by universe-level constraints (data, prop, theorem, proof).
        let data_params: Vec<_> = params
            .iter()
            .filter(|(_, mc)| !mc.is_some_and(|c| is_type_universe(c)))
            .collect();
        let param_types: Vec<CType> = data_params
            .iter()
            .map(|(_, mc)| {
                mc.map_or(Ok(CType::Int64), |c| {
                    constraint_to_ctype(c, union_names, struct_names)
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ret_type = match m_ret {
            Some(t) if !is_type_universe(t) => constraint_to_ctype(t, union_names, struct_names)?,
            _ => infer_ret_ctype(body, &param_types),
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

/// Returns true if the constraint represents a type-level universe
/// (data, prop, theorem, proof) — parameters with these constraints
/// should be stripped from C function signatures.
pub fn is_type_universe(t: &crate::core::syntax::Term<'_>) -> bool {
    match t {
        crate::core::syntax::Term::Builtin(name) | crate::core::syntax::Term::Named(name) => {
            matches!(*name, "data" | "prop" | "theorem" | "proof")
        }
        crate::core::syntax::Term::Universe(_) => true,
        _ => false,
    }
}

/// Map a constraint Term to its C type.  Recognizes builtin type names,
/// user-defined struct types, and union types;
/// returns an error for unrecognized types.
pub fn constraint_to_ctype(
    t: &crate::core::syntax::Term<'_>,
    union_names: &HashSet<String>,
    struct_names: &HashSet<String>,
) -> Result<CType, String> {
    match t {
        crate::core::syntax::Term::Builtin(name) if *name == "str" => Ok(CType::Str),
        crate::core::syntax::Term::Builtin(name) | crate::core::syntax::Term::Named(name)
            if struct_names.contains(&name.to_string()) =>
        {
            Ok(CType::Struct(name.to_string()))
        }
        crate::core::syntax::Term::Builtin(name) | crate::core::syntax::Term::Named(name)
            if union_names.contains(&name.to_string()) =>
        {
            Ok(CType::Union(name.to_string()))
        }
        crate::core::syntax::Term::Builtin(_)
        | crate::core::syntax::Term::Named(_)
        | crate::core::syntax::Term::LitInt(_)
        | crate::core::syntax::Term::LitBool(_)
        | crate::core::syntax::Term::Var(_)
        | crate::core::syntax::Term::Universe(_) => Ok(CType::Int64),
        crate::core::syntax::Term::Refine(_, parent, _) => {
            constraint_to_ctype(parent, union_names, struct_names)
        }
        crate::core::syntax::Term::Annot(_, c) => constraint_to_ctype(c, union_names, struct_names),
        // Handle union type applications like `Option int` → Union("Option")
        crate::core::syntax::Term::App(head, _) => {
            if let crate::core::syntax::Term::Builtin(name)
            | crate::core::syntax::Term::Named(name) = *head
            {
                if union_names.contains(&name.to_string()) {
                    return Ok(CType::Union(name.to_string()));
                }
                if struct_names.contains(&name.to_string()) {
                    return Ok(CType::Struct(name.to_string()));
                }
            }
            Ok(CType::Int64)
        }
        crate::core::syntax::Term::Pi(_, _, _)
        | crate::core::syntax::Term::Lam(_)
        | crate::core::syntax::Term::Let(..)
        | crate::core::syntax::Term::IfThenElse(..)
        | crate::core::syntax::Term::ByProof(..)
        | crate::core::syntax::Term::AutoProof
        | crate::core::syntax::Term::RefParam
        | crate::core::syntax::Term::PrimOp(_)
        | crate::core::syntax::Term::UnionDef(..)
        | crate::core::syntax::Term::Variant(..)
        | crate::core::syntax::Term::Match(..)
        | crate::core::syntax::Term::StructDef(..)
        | crate::core::syntax::Term::StructCons(..)
        | crate::core::syntax::Term::StructProj(..) => Ok(CType::Int64),
        _ => Err(format!("Cannot map constraint {:?} to C type", t)),
    }
}
