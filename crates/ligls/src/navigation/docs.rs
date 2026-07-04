use tower_lsp::lsp_types as lsp;

use super::{NavSymbol, SymbolKind};

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

pub(super) fn doc_comment_before(source: &str, start: usize) -> Option<String> {
    if let Some(doc) = block_doc_comment_before(source, start) {
        return Some(doc);
    }

    let mut docs = Vec::new();
    for line in source[..start].lines().rev() {
        let trimmed = line.trim_start();
        if let Some(doc) = trimmed.strip_prefix("-- |") {
            docs.push(doc.trim_start().to_string());
            continue;
        }
        break;
    }
    if docs.is_empty() {
        None
    } else {
        docs.reverse();
        Some(docs.join("\n"))
    }
}

fn block_doc_comment_before(source: &str, start: usize) -> Option<String> {
    let end = doc_comment_end_before(source, start)?;
    let before_close = end.checked_sub(2)?;
    let open = source[..before_close].rfind("{-")?;
    let raw = &source[open..end];
    if raw.starts_with("{-!") || !raw.ends_with("-}") {
        return None;
    }
    let doc = clean_block_doc(&raw[2..raw.len() - 2]);
    (!doc.trim().is_empty()).then_some(doc)
}

fn doc_comment_end_before(source: &str, start: usize) -> Option<usize> {
    let mut index = start;
    index = skip_horizontal_space_back(source, index);
    if source[..index].ends_with('\n') {
        index -= 1;
        if source[..index].ends_with('\r') {
            index -= 1;
        }
        index = skip_horizontal_space_back(source, index);
    }
    source[..index].ends_with("-}").then_some(index)
}

fn skip_horizontal_space_back(source: &str, mut index: usize) -> usize {
    while index > 0 {
        match source.as_bytes()[index - 1] {
            b' ' | b'\t' | b'\r' | b'\x0c' => index -= 1,
            _ => break,
        }
    }
    index
}

fn clean_block_doc(raw: &str) -> String {
    let mut lines: Vec<&str> = raw.lines().collect();
    while lines.first().is_some_and(|line| line.trim().is_empty()) {
        lines.remove(0);
    }
    while lines.last().is_some_and(|line| line.trim().is_empty()) {
        lines.pop();
    }

    let indent = lines
        .iter()
        .filter(|line| !line.trim().is_empty())
        .map(|line| {
            line.bytes()
                .take_while(|b| matches!(b, b' ' | b'\t'))
                .count()
        })
        .min()
        .unwrap_or(0);

    lines
        .into_iter()
        .map(|line| line.get(indent..).unwrap_or(line).trim_end())
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}
