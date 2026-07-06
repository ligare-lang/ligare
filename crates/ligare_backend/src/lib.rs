use std::path::{Path, PathBuf};

use ligare_ast::core::syntax::Term;
use ligare_front::front::parser::TopLevel;
use ligare_support::diagnostic::Diagnostic;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeDefKind {
    Enum,
    Struct,
}

#[derive(Clone, Copy, Debug)]
pub struct TypeDef<'a, 'bump> {
    pub kind: TypeDefKind,
    pub name: &'bump str,
    pub body: &'bump Term<'bump>,
    _marker: std::marker::PhantomData<&'a ()>,
}

#[derive(Clone, Copy, Debug)]
pub struct CodegenInput<'a, 'bump> {
    pub tops: &'a [TopLevel<'bump>],
    pub raw_defs: &'a [TopLevel<'bump>],
    pub enum_types: &'a [(&'bump str, &'bump Term<'bump>)],
    pub struct_types: &'a [(&'bump str, &'bump Term<'bump>)],
}

impl<'a, 'bump> CodegenInput<'a, 'bump> {
    pub fn type_defs(&self) -> impl Iterator<Item = TypeDef<'a, 'bump>> + 'a {
        self.enum_types
            .iter()
            .map(|(name, body)| TypeDef {
                kind: TypeDefKind::Enum,
                name,
                body,
                _marker: std::marker::PhantomData,
            })
            .chain(self.struct_types.iter().map(|(name, body)| TypeDef {
                kind: TypeDefKind::Struct,
                name,
                body,
                _marker: std::marker::PhantomData,
            }))
    }
}

pub trait Backend: Send + Sync {
    fn name(&self) -> &'static str;

    fn source_extension(&self) -> &'static str;

    fn emit_source(&self, input: CodegenInput<'_, '_>) -> Result<String, Diagnostic>;

    fn emit_eval_source(&self, input: CodegenInput<'_, '_>) -> Result<Option<String>, Diagnostic>;

    fn compile_source(&self, _source: &str, _output_path: &Path) -> Result<PathBuf, CompileError> {
        Err(CompileError::UnsupportedOperation {
            backend: self.name(),
            operation: "native compilation",
        })
    }

    fn run_eval_source(&self, _source: &str) -> Result<String, CompileError> {
        Err(CompileError::UnsupportedOperation {
            backend: self.name(),
            operation: "eval execution",
        })
    }
}

pub struct BackendRegistry {
    backends: &'static [&'static dyn Backend],
}

impl BackendRegistry {
    pub const fn new(backends: &'static [&'static dyn Backend]) -> Self {
        Self { backends }
    }

    pub fn get(&self, name: &str) -> Option<&'static dyn Backend> {
        self.backends
            .iter()
            .copied()
            .find(|backend| backend.name() == name)
    }

    pub fn names(&self) -> impl Iterator<Item = &'static str> + '_ {
        self.backends.iter().map(|backend| backend.name())
    }

    pub fn default_backend(&self) -> Option<&'static dyn Backend> {
        self.backends.first().copied()
    }
}

#[derive(Debug)]
pub enum CompileError {
    Io(std::io::Error),
    CompilerNotFound,
    CompileFailed {
        status: std::process::ExitStatus,
        stderr: String,
    },
    RunFailed {
        status: std::process::ExitStatus,
        stderr: String,
    },
    UnsupportedOperation {
        backend: &'static str,
        operation: &'static str,
    },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::Io(e) => write!(f, "I/O error: {}", e),
            CompileError::CompilerNotFound => write!(f, "compiler not found in PATH"),
            CompileError::CompileFailed { status, stderr } => {
                write!(f, "compilation failed ({}): {}", status, stderr)
            }
            CompileError::RunFailed { status, stderr } => {
                write!(f, "eval execution failed ({}): {}", status, stderr)
            }
            CompileError::UnsupportedOperation { backend, operation } => {
                write!(f, "backend `{backend}` does not support {operation}")
            }
        }
    }
}

impl std::error::Error for CompileError {}

impl From<std::io::Error> for CompileError {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}
