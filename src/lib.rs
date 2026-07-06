pub mod config {
    pub use ligare_support::config::*;
}

pub mod diagnostic {
    pub use ligare_support::diagnostic::*;
}

pub mod core {
    pub use ligare_ast::core::debruijn;
    pub use ligare_ast::core::desugar;
    pub use ligare_ast::core::pool;
    pub use ligare_ast::core::syntax;
    pub use ligare_kernel::core::eval;
    pub use ligare_kernel::core::semantics;
    pub use ligare_kernel::core::whnf;
}

pub mod pretty {
    pub use ligare_ast::pretty::*;
}

pub mod front {
    pub use ligare_front::front::lexer;
    pub use ligare_front::front::parser;
}

pub mod checker {
    pub use ligare_kernel::checker::builtin;
    pub use ligare_kernel::checker::context;
    pub use ligare_kernel::checker::erase;
    pub use ligare_kernel::checker::infer;
    pub use ligare_kernel::checker::prove;
    pub use ligare_kernel::checker::{CheckMode, MethodInstance, TypeChecker, check};
}

pub mod backend;
pub mod compiler;
pub mod package;
