pub use ligare_backend::{
    Backend, BackendRegistry, CodegenInput, CompileError, TypeDef, TypeDefKind,
};
pub use ligare_backend_c::{c, compile, ir};

static BACKENDS: [&'static dyn Backend; 1] = [&ligare_backend_c::C_BACKEND];

pub fn registry() -> BackendRegistry {
    BackendRegistry::new(&BACKENDS)
}

pub fn backend_named(name: &str) -> Option<&'static dyn Backend> {
    registry().get(name)
}

pub fn default_backend() -> &'static dyn Backend {
    registry()
        .default_backend()
        .expect("at least one backend must be registered")
}
