//! LSP-facing parsing support for Ligare.
//!
//! This crate keeps recovery-only nodes and parse errors out of the compiler
//! AST. Successful syntax nodes reuse `ligare`'s parser-level AST types.

mod ast;
mod cache;
mod completion;
mod document;
mod navigation;
mod parse;
mod semantic;
mod server;
mod workspace;

#[cfg(test)]
mod tests;

pub use ast::{Ast, AstNode, ErrorNode, ParseError};
pub use completion::completion_items_for_source;
pub use document::{DiagnosticCheck, formatting_edits, lsp_diagnostics_for_source};
pub use parse::parse_program_lsp;
pub use semantic::{semantic_tokens_for_source_text, semantic_tokens_legend};
pub use server::{Backend, DiagnosticPublisher, DiagnosticService};
