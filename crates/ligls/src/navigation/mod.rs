use std::ops::Range;

use tower_lsp::lsp_types as lsp;

use crate::completion::{Constraint, Signature, SymbolKind, TokenSpan};
use crate::workspace::ModuleKey;

mod docs;
mod document;
mod index;
mod spans;
mod symbols;

use self::docs::doc_comment_before;

#[derive(Debug, Clone)]
pub(crate) struct SourceDocument {
    pub(crate) uri: lsp::Url,
    pub(crate) text: String,
}

#[derive(Debug, Clone)]
struct NavSymbol {
    name: String,
    detail: String,
    constraint: Option<Constraint>,
    signature: Option<Signature>,
    kind: SymbolKind,
    uri: lsp::Url,
    range: lsp::Range,
    byte_start: usize,
    module_key: ModuleKey,
    imported_path: Option<Vec<String>>,
    doc: Option<String>,
    scope: Option<Scope>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Scope {
    uri: lsp::Url,
    start: usize,
    end: usize,
}

#[derive(Debug)]
struct IndexedDocument {
    uri: lsp::Url,
    text: String,
    tokens: Vec<TokenSpan>,
    module_key: ModuleKey,
    imports: Vec<ImportRef>,
    symbols: Vec<NavSymbol>,
}

#[derive(Debug, Clone)]
struct ImportRef {
    path: Vec<String>,
    name: String,
    alias_span: Option<Range<usize>>,
    start: usize,
    end: usize,
}

#[derive(Debug)]
struct NavIndex {
    docs: Vec<IndexedDocument>,
    symbols: Vec<NavSymbol>,
}

#[derive(Debug, Clone)]
struct Reference {
    name: String,
    offset: usize,
    use_path: Option<Vec<String>>,
}

pub(crate) fn definition_for_documents(
    documents: &[SourceDocument],
    uri: &lsp::Url,
    position: lsp::Position,
) -> Option<lsp::GotoDefinitionResponse> {
    let index = NavIndex::build(documents, uri);
    let doc = index.document(uri)?;
    let reference = doc.reference_at(position)?;
    let target = index.resolve_reference(doc, &reference)?;
    Some(lsp::GotoDefinitionResponse::Scalar(lsp::Location {
        uri: target.uri.clone(),
        range: target.range,
    }))
}

pub(crate) fn hover_for_documents(
    documents: &[SourceDocument],
    uri: &lsp::Url,
    position: lsp::Position,
) -> Option<lsp::Hover> {
    let index = NavIndex::build(documents, uri);
    let doc = index.document(uri)?;
    let reference = doc.reference_at(position)?;
    let symbol = index.resolve_reference(doc, &reference)?;
    Some(symbol.hover())
}

#[allow(deprecated)]
pub(crate) fn document_symbols_for_documents(
    documents: &[SourceDocument],
    uri: &lsp::Url,
) -> Option<lsp::DocumentSymbolResponse> {
    let index = NavIndex::build(documents, uri);
    let doc = index.document(uri)?;
    let symbols = doc
        .symbols
        .iter()
        .filter(|symbol| symbol.uri == *uri && symbol.scope.is_none())
        .map(|symbol| lsp::SymbolInformation {
            name: symbol.name.clone(),
            kind: symbol.kind.lsp_symbol_kind(),
            tags: None,
            deprecated: None,
            location: lsp::Location {
                uri: symbol.uri.clone(),
                range: symbol.range,
            },
            container_name: None,
        })
        .collect::<Vec<_>>();
    Some(lsp::DocumentSymbolResponse::Flat(symbols))
}

pub(crate) fn references_for_documents(
    documents: &[SourceDocument],
    uri: &lsp::Url,
    position: lsp::Position,
    include_declaration: bool,
) -> Option<Vec<lsp::Location>> {
    let index = NavIndex::build(documents, uri);
    let doc = index.document(uri)?;
    let reference = doc.reference_at(position)?;
    let target = index.resolve_reference(doc, &reference)?;
    Some(index.references_to(target, include_declaration))
}

fn same_symbol(left: &NavSymbol, right: &NavSymbol) -> bool {
    left.uri == right.uri
        && left.range.start == right.range.start
        && left.range.end == right.range.end
        && left.name == right.name
}

fn unwrap_public<'a, 'bump>(
    top: &'a ligare::front::parser::TopLevel<'bump>,
) -> &'a ligare::front::parser::TopLevel<'bump> {
    use ligare::front::parser::TopLevel;

    match top {
        TopLevel::TLPublic(inner) => unwrap_public(inner),
        TopLevel::TLAttributed(_, inner, _) => unwrap_public(inner),
        other => other,
    }
}
