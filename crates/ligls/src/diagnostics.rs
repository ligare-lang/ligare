use bumpalo::Bump;
use ligare::checker::CheckMode;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;
use ligare::diagnostic::{Diagnostic as CompilerDiagnostic, Span};
use tower_lsp::lsp_types as lsp;

use crate::text::offset_to_position;
use crate::{ParseError, parse_program_lsp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticCheck {
    Fast,
    Full,
}

impl From<DiagnosticCheck> for CheckMode {
    fn from(value: DiagnosticCheck) -> Self {
        match value {
            DiagnosticCheck::Fast => CheckMode::Fast,
            DiagnosticCheck::Full => CheckMode::Full,
        }
    }
}

pub fn lsp_diagnostics_for_source(source: &str, check: DiagnosticCheck) -> Vec<lsp::Diagnostic> {
    let bump = Bump::new();
    let arena = TermArena::new(&bump);
    let (ast, parse_errors) = parse_program_lsp(source, &bump, &arena);
    let mut diagnostics = parse_errors
        .into_iter()
        .map(|error| parse_error_to_lsp(source, error))
        .collect::<Vec<_>>();

    let tops = ast.top_levels().cloned().collect::<Vec<_>>();
    let mut compiler = Compiler::new(&bump, &arena);
    diagnostics.extend(
        compiler
            .check_top_levels_for_diagnostics(tops, "<lsp>", source, check.into())
            .into_iter()
            .map(|diagnostic| compiler_diagnostic_to_lsp(source, diagnostic)),
    );

    dedup_diagnostics(diagnostics)
}

pub(crate) fn parse_error_to_lsp(source: &str, error: ParseError) -> lsp::Diagnostic {
    lsp::Diagnostic {
        range: span_to_lsp_range(source, error.span),
        severity: Some(lsp::DiagnosticSeverity::ERROR),
        source: Some("ligare".to_string()),
        message: error.message,
        ..Default::default()
    }
}

pub(crate) fn compiler_diagnostic_to_lsp(
    source: &str,
    diagnostic: CompilerDiagnostic,
) -> lsp::Diagnostic {
    lsp::Diagnostic {
        range: span_to_lsp_range(source, diagnostic.span.unwrap_or(0..0)),
        severity: Some(lsp::DiagnosticSeverity::ERROR),
        source: Some("ligare".to_string()),
        message: diagnostic.message,
        ..Default::default()
    }
}

pub(crate) fn dedup_diagnostics(diagnostics: Vec<lsp::Diagnostic>) -> Vec<lsp::Diagnostic> {
    let mut seen = std::collections::HashSet::new();
    let mut unique = Vec::new();
    for diagnostic in diagnostics {
        let key = (
            diagnostic.range.start.line,
            diagnostic.range.start.character,
            diagnostic.range.end.line,
            diagnostic.range.end.character,
            diagnostic_severity_key(diagnostic.severity),
            diagnostic.message.clone(),
        );
        if seen.insert(key) {
            unique.push(diagnostic);
        }
    }
    unique
}

fn diagnostic_severity_key(severity: Option<lsp::DiagnosticSeverity>) -> u8 {
    match severity {
        Some(lsp::DiagnosticSeverity::ERROR) => 1,
        Some(lsp::DiagnosticSeverity::WARNING) => 2,
        Some(lsp::DiagnosticSeverity::INFORMATION) => 3,
        Some(lsp::DiagnosticSeverity::HINT) => 4,
        _ => 0,
    }
}

fn span_to_lsp_range(source: &str, span: Span) -> lsp::Range {
    lsp::Range {
        start: offset_to_position(source, span.start),
        end: offset_to_position(source, span.end.max(span.start)),
    }
}
