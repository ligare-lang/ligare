//! Centralised constants for names that are used across multiple modules.
//! Format strings / templates stay in their respective modules as-is.

// ── Universe display names ──

pub const UNIVERSE_DATA: &str = "data";
pub const UNIVERSE_PROP: &str = "prop";
pub const UNIVERSE_THEOREM: &str = "theorem";
pub const UNIVERSE_PROOF: &str = "proof";

// ── Builtin type names (also used as keywords / constraints) ──

pub const BUILTIN_INT: &str = "int";
pub const BUILTIN_BOOL: &str = "bool";
pub const BUILTIN_STR: &str = "str";
pub const BUILTIN_IO: &str = "IO";
pub const BUILTIN_UNIT: &str = "Unit";
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
