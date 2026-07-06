//! C code generation backend — fully OOP design.
//!
//! Architecture:
//! ```text
//! CodeGenerator (trait)
//!   └── CEmitter (orchestrator)
//!         ├── TypeAnalyzer   — type maps, typedef emission, TypeMapper impl
//!         ├── NameResolver   — escaping, collection, lambda analysis
//!         ├── ExpressionEmitter — Term → C expression translation
//!         ├── MatchEmitter   — match → switch translation
//!         └── EmitCtx        — mutable per-expression state
//! ```
//!
//! Usage:
//! ```ignore
//! use ligare::backend::c::{CEmitter, CodeGenerator};
//! let emitter = CEmitter::new(struct_types, enum_types, raw_defs)?;
//! let c_source = emitter.generate(tops, raw_defs, struct_types, enum_types)?;
//! ```

pub mod context;
pub mod emitter;
pub mod expr;
pub mod match_emit;
pub mod names;
pub mod types;
mod value;

#[cfg(test)]
mod tests;

// ── Re-exports for convenience ──

pub use context::EmitCtx;
pub use emitter::{CEmitOptions, CEmitter, CTarget, CodeGenerator};
pub use expr::ExpressionEmitter;
pub use match_emit::MatchEmitter;
pub use names::NameResolver;
pub use types::{EnumInfo, StructInfo, TypeAnalyzer, TypeMapper, VariantInfo};

use crate::diagnostic::Diagnostic;
use ligare_backend::CodegenInput;

/// Convenience wrapper: produce a complete C source file.
///
/// For new code, prefer going through the backend registry.
pub fn emit_c(input: CodegenInput<'_, '_>) -> Result<String, Diagnostic> {
    let emitter = CEmitter::new(input.struct_types, input.enum_types, input.raw_defs)?;
    emitter.generate(
        input.tops,
        input.raw_defs,
        input.struct_types,
        input.enum_types,
    )
}

pub fn emit_c_with_options(
    input: CodegenInput<'_, '_>,
    options: CEmitOptions,
) -> Result<String, Diagnostic> {
    let emitter = CEmitter::new_with_options(
        input.struct_types,
        input.enum_types,
        input.raw_defs,
        options,
    )?;
    emitter.generate(
        input.tops,
        input.raw_defs,
        input.struct_types,
        input.enum_types,
    )
}

/// Produce a temporary eval-only C source file, if the program contains `#eval`.
pub fn emit_eval_c(input: CodegenInput<'_, '_>) -> Result<Option<String>, Diagnostic> {
    let emitter = CEmitter::new(input.struct_types, input.enum_types, input.raw_defs)?;
    emitter.generate_eval(
        input.tops,
        input.raw_defs,
        input.struct_types,
        input.enum_types,
    )
}
