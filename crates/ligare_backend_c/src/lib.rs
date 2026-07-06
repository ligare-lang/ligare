use std::path::{Path, PathBuf};

use ligare_backend::{Backend, CodegenInput, CompileError};
use ligare_support::diagnostic::Diagnostic;

pub mod backend;

pub use backend::{c, compile, ir};

pub mod checker {
    pub use ligare_kernel::checker::builtin;
}

pub mod config {
    pub use ligare_support::config::*;
}

pub mod core {
    pub use ligare_ast::core::debruijn;
    pub use ligare_ast::core::pool;
    pub use ligare_ast::core::syntax;
    pub use ligare_kernel::core::semantics;
}

pub mod diagnostic {
    pub use ligare_support::diagnostic::*;
}

pub mod front {
    pub use ligare_front::front::parser;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CBackend;

pub static C_BACKEND: CBackend = CBackend;

impl Backend for CBackend {
    fn name(&self) -> &'static str {
        "c"
    }

    fn source_extension(&self) -> &'static str {
        "c"
    }

    fn emit_source(&self, input: CodegenInput<'_, '_>) -> Result<String, Diagnostic> {
        c::emit_c(input)
    }

    fn emit_eval_source(&self, input: CodegenInput<'_, '_>) -> Result<Option<String>, Diagnostic> {
        c::emit_eval_c(input)
    }

    fn compile_source(&self, source: &str, output_path: &Path) -> Result<PathBuf, CompileError> {
        compile::compile_c(source, output_path)
    }

    fn run_eval_source(&self, source: &str) -> Result<String, CompileError> {
        compile::compile_and_run_c(source)
    }
}
