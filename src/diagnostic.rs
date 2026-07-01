use annotate_snippets::{AnnotationKind, Level, Renderer, Snippet};

/// A source span: byte offset range in the source text.
pub type Span = std::ops::Range<usize>;

/// A structured diagnostic message with optional source span information.
///
/// Replaces bare `String` errors in public-facing compiler APIs so callers
/// can highlight the relevant source location without parsing error messages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    pub span: Option<Span>,
    pub file: Option<String>,
    pub source: Option<String>,
}

impl Diagnostic {
    /// Create a diagnostic with just a message (no span).
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            span: None,
            file: None,
            source: None,
        }
    }

    /// Create a diagnostic with both a message and a source span.
    pub fn with_span(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span: Some(span),
            file: None,
            source: None,
        }
    }

    /// Attach source context for line/column and caret rendering.
    pub fn with_source(mut self, file: impl Into<String>, source: impl Into<String>) -> Self {
        self.file = Some(file.into());
        self.source = Some(source.into());
        self
    }

    /// Attach source context if this diagnostic has no context yet.
    pub fn with_source_if_missing(
        mut self,
        file: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        if self.file.is_none() && self.source.is_none() {
            self.file = Some(file.into());
            self.source = Some(source.into());
        }
        self
    }

    fn render_snippet(&self) -> Option<String> {
        let span = self.span.as_ref()?;
        let source = self.source.as_deref()?;
        let start = span.start.min(source.len());
        let end = span.end.min(source.len()).max(start);
        let origin = self.file.as_deref().unwrap_or("<source>");
        let report = &[Level::ERROR.primary_title(&self.message).element(
            Snippet::source(source)
                .path(origin)
                .annotation(AnnotationKind::Primary.span(start..end)),
        )];
        Some(Renderer::plain().render(report).to_string())
    }
}

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(rendered) = self.render_snippet() {
            return write!(f, "{rendered}");
        }
        if let Some(span) = &self.span {
            return write!(f, "{} (at {}..{})", self.message, span.start, span.end);
        }
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for Diagnostic {}

impl From<String> for Diagnostic {
    fn from(message: String) -> Self {
        Self::new(message)
    }
}

impl From<&str> for Diagnostic {
    fn from(message: &str) -> Self {
        Self::new(message)
    }
}
