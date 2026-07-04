//! Centralised constants for names that are used across multiple modules.
//! Format strings / templates stay in their respective modules as-is.

// ── Universe display names ──

pub const UNIVERSE_DATA: &str = "data";
pub const UNIVERSE_PROP: &str = "prop";
pub const UNIVERSE_THEOREM: &str = "theorem";
pub const UNIVERSE_PROOF: &str = "proof";

// ── Builtin type names (also used as keywords / constraints) ──

pub const BUILTIN_INT: &str = "int";
pub const BUILTIN_I8: &str = "i8";
pub const BUILTIN_I16: &str = "i16";
pub const BUILTIN_I32: &str = "i32";
pub const BUILTIN_I64: &str = "i64";
pub const BUILTIN_U8: &str = "u8";
pub const BUILTIN_U16: &str = "u16";
pub const BUILTIN_U32: &str = "u32";
pub const BUILTIN_U64: &str = "u64";
pub const BUILTIN_C_INT: &str = "c_int";
pub const BUILTIN_C_UINT: &str = "c_uint";
pub const BUILTIN_PTR: &str = "ptr";
pub const BUILTIN_PTR_CAST: &str = "ptr_cast";
pub const BUILTIN_BOOL: &str = "bool";
pub const BUILTIN_STR: &str = "str";
pub const BUILTIN_IO: &str = "IO";
pub const BUILTIN_UNIT: &str = "()";
pub const BUILTIN_DATA: &str = "data";
pub const BUILTIN_PROP: &str = "prop";
pub const BUILTIN_THEOREM: &str = "theorem";
pub const BUILTIN_PROOF: &str = "proof";

// ── Builtin logic names ──

pub const BUILTIN_AND: &str = "and";
pub const BUILTIN_OR: &str = "or";
pub const BUILTIN_NOT: &str = "not";
pub const BUILTIN_IMPLIES: &str = "implies";

// ── Standard-library intrinsic names ──

pub const STD_PRIMITIVE_MODULE: &str = "std::primitive";

pub fn canonical_builtin_name(name: &str) -> &str {
    match name {
        "std::primitive::int" => BUILTIN_INT,
        "std::primitive::i8" => BUILTIN_I8,
        "std::primitive::i16" => BUILTIN_I16,
        "std::primitive::i32" => BUILTIN_I32,
        "std::primitive::i64" => BUILTIN_I64,
        "std::primitive::u8" => BUILTIN_U8,
        "std::primitive::u16" => BUILTIN_U16,
        "std::primitive::u32" => BUILTIN_U32,
        "std::primitive::u64" => BUILTIN_U64,
        "std::primitive::c_int" => BUILTIN_C_INT,
        "std::primitive::c_uint" => BUILTIN_C_UINT,
        "std::primitive::ptr" => BUILTIN_PTR,
        "std::primitive::ptr_cast" => BUILTIN_PTR_CAST,
        "std::primitive::bool" => BUILTIN_BOOL,
        "std::primitive::str" => BUILTIN_STR,
        "std::primitive::IO" => BUILTIN_IO,
        "std::meta::Expr" => "Expr",
        "std::meta::Definitions" => "Definitions",
        _ => name,
    }
}

pub fn is_builtin_name(name: &str, builtin: &str) -> bool {
    canonical_builtin_name(name) == builtin
}

pub fn is_std_intrinsic_name(name: &str) -> bool {
    matches!(
        name,
        "std::primitive::int"
            | "std::primitive::i8"
            | "std::primitive::i16"
            | "std::primitive::i32"
            | "std::primitive::i64"
            | "std::primitive::u8"
            | "std::primitive::u16"
            | "std::primitive::u32"
            | "std::primitive::u64"
            | "std::primitive::c_int"
            | "std::primitive::c_uint"
            | "std::primitive::ptr"
            | "std::primitive::ptr_cast"
            | "std::primitive::bool"
            | "std::primitive::str"
            | "std::primitive::IO"
    )
}

// ── Logic intro / elim names ──

pub const AND_INTRO: &str = "∧-intro";
pub const AND_ELIM_LEFT: &str = "∧-elim-left";

// ── Code generation attributes ──

pub const GLOBAL_ALLOCATOR_ATTR: &str = "global_allocator";
pub const GLOBAL_ALLOCATOR_NAME_PREFIX: &str = "__ligare_global_allocator__";
pub const COMPILER_INTRINSIC_ATTR: &str = "compiler_intrinsic";
pub const COMPILER_BUILTIN_ATTRIBUTE_ATTR: &str = "compiler_builtin_attribute";
pub const TERMINATING_ATTR: &str = "terminating";
pub const TACTIC_ATTR: &str = "tactic";
pub const CUSTOM_ATTRIBUTE_ATTR: &str = "attr";
pub const DERIVE_ATTR: &str = "derive";
