//! LSP-facing parsing support for Ligare.
//!
//! This crate keeps recovery-only nodes and parse errors out of the compiler
//! AST. Successful syntax nodes reuse `ligare`'s parser-level AST types.

mod ast;
mod backend;
mod cache;
mod completion;
mod diagnostics;
mod formatting;
mod navigation;
mod parse;
mod project;
mod semantic;
mod service;
mod text;

#[cfg(test)]
mod tests;

pub use ast::{Ast, AstNode, ErrorNode, ParseError};
pub use backend::Backend;
pub use completion::completion_items_for_source;
pub use diagnostics::{DiagnosticCheck, lsp_diagnostics_for_source};
pub use formatting::formatting_edits;
pub use parse::parse_program_lsp;
pub use semantic::{semantic_tokens_for_source_text, semantic_tokens_legend};
pub use service::{DiagnosticPublisher, DiagnosticService};
