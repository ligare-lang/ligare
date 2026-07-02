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

// ── Logic intro / elim names ──

pub const AND_INTRO: &str = "∧-intro";
pub const AND_ELIM_LEFT: &str = "∧-elim-left";

// ── Code generation attributes ──

pub const GLOBAL_ALLOCATOR_ATTR: &str = "global_allocator";
pub const GLOBAL_ALLOCATOR_NAME_PREFIX: &str = "__ligare_global_allocator__";
