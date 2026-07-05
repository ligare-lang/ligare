use tower_lsp::lsp_types as lsp;

use super::{NavSymbol, SymbolKind};
pub(super) use ligare_doc::doc_comment_before;

impl NavSymbol {
    pub(super) fn hover(&self) -> lsp::Hover {
        let mut body = format!("```ligare\n{} : {}\n```", self.name, self.constraint_text());
        if let Some(doc) = &self.doc
            && !doc.trim().is_empty()
        {
            body.push_str("\n\n");
            body.push_str(doc.trim());
        }
        lsp::Hover {
            contents: lsp::HoverContents::Markup(lsp::MarkupContent {
                kind: lsp::MarkupKind::Markdown,
                value: body,
            }),
            range: Some(self.range),
        }
    }

    fn constraint_text(&self) -> String {
        self.signature
            .as_ref()
            .map(|sig| sig.whole.display.clone())
            .or_else(|| {
                self.constraint
                    .as_ref()
                    .map(|constraint| constraint.display.clone())
            })
            .unwrap_or_else(|| self.detail.clone())
    }
}

impl SymbolKind {
    pub(super) fn lsp_symbol_kind(self) -> lsp::SymbolKind {
        match self {
            SymbolKind::Local | SymbolKind::Value => lsp::SymbolKind::VARIABLE,
            SymbolKind::Function => lsp::SymbolKind::FUNCTION,
            SymbolKind::Constructor => lsp::SymbolKind::CONSTRUCTOR,
            SymbolKind::Type => lsp::SymbolKind::STRUCT,
            SymbolKind::Import => lsp::SymbolKind::NAMESPACE,
            SymbolKind::Module | SymbolKind::Keyword => lsp::SymbolKind::MODULE,
        }
    }
}
