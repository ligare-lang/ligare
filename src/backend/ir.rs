//! Minimal IR types for C code generation.
//!
//! `CType` maps term-level data to C declarations.
//! `FunSig` records the erased C types of function parameters and return
//! values, populated during erasure and consumed by the C backend.

/// Concrete C type — only the data-relevant ones.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CType {
    Int64,
    Str,
}

impl CType {
    pub fn c_name(self) -> &'static str {
        match self {
            CType::Int64 => "int64_t",
            CType::Str => "const char*",
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
    pub ret_type: Option<CType>,
}

impl FunSig {
    /// Extract a function's C signature from its Term representation,
    /// before erasure strips the constraint information.
    pub fn from_func(
        params: &[(
            crate::core::syntax::Name<'_>,
            Option<&crate::core::syntax::Term<'_>>,
        )],
        m_ret: Option<&crate::core::syntax::Term<'_>>,
    ) -> Self {
        let param_types: Vec<CType> = params
            .iter()
            .map(|(_, mc)| mc.map_or(CType::Int64, constraint_to_ctype))
            .collect();
        let ret_type = m_ret.map(constraint_to_ctype);
        FunSig {
            param_types,
            ret_type,
        }
    }
}

/// Map a constraint Term to its C type.  Only recognizes builtin type
/// names; everything else defaults to Int64 (the constraint checker
/// already validated correctness, so this is just a hint for codegen).
pub fn constraint_to_ctype(t: &crate::core::syntax::Term<'_>) -> CType {
    match t {
        crate::core::syntax::Term::Builtin(name) => match *name {
            "str" => CType::Str,
            _ => CType::Int64,
        },
        _ => CType::Int64,
    }
}
