use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::front::lexer::Token;
use tower_lsp::lsp_types as lsp;

use super::{
    IndexedDocument, NavIndex, NavSymbol, Reference, SourceDocument, SymbolKind, same_symbol,
};
use crate::workspace::{fallback_imported_module_keys, project_context_for_uri};

impl NavIndex {
    pub(super) fn build(documents: &[SourceDocument], root_uri: &lsp::Url) -> Self {
        let project = project_context_for_uri(root_uri);
        let mut docs = Vec::new();
        let mut all_symbols = Vec::new();

        for document in documents {
            let indexed = IndexedDocument::build(document, project.as_ref());
            all_symbols.extend(indexed.symbols.iter().cloned());
            docs.push(indexed);
        }

        Self {
            docs,
            symbols: all_symbols,
        }
    }

    pub(super) fn document(&self, uri: &lsp::Url) -> Option<&IndexedDocument> {
        self.docs.iter().find(|doc| &doc.uri == uri)
    }

    pub(super) fn resolve_reference<'a>(
        &'a self,
        doc: &'a IndexedDocument,
        reference: &Reference,
    ) -> Option<&'a NavSymbol> {
        if let Some(path) = &reference.use_path {
            if let Some(symbol) = self.symbol_for_import_path(doc, path) {
                return Some(symbol);
            }
            if let Some(module) = self.module_for_path(path) {
                return Some(module);
            }
        }

        if reference.name.contains('.')
            && let Some(symbol) = self.visible_symbol(doc, &reference.name, reference.offset)
        {
            return Some(symbol);
        }

        if let Some(local) = self.local_symbol(doc, &reference.name, reference.offset) {
            return Some(local);
        }

        if let Some(import) = doc.import_for_name(&reference.name)
            && let Some(symbol) = self.symbol_for_import_path(doc, &import)
        {
            return Some(symbol);
        }

        self.visible_symbol(doc, &reference.name, reference.offset)
            .or_else(|| self.module_for_path(std::slice::from_ref(&reference.name)))
            .or_else(|| self.builtin_symbol(doc, &reference.name))
    }

    fn local_symbol<'a>(
        &'a self,
        doc: &IndexedDocument,
        name: &str,
        offset: usize,
    ) -> Option<&'a NavSymbol> {
        self.symbols
            .iter()
            .filter(|symbol| symbol.name == name && symbol.uri == doc.uri)
            .filter(|symbol| {
                symbol.scope.as_ref().is_some_and(|scope| {
                    scope.uri == doc.uri && scope.start <= offset && offset <= scope.end
                })
            })
            .filter(|symbol| symbol.byte_start <= offset)
            .max_by_key(|symbol| symbol.byte_start)
    }

    fn visible_symbol<'a>(
        &'a self,
        doc: &IndexedDocument,
        name: &str,
        offset: usize,
    ) -> Option<&'a NavSymbol> {
        self.symbols
            .iter()
            .filter(|symbol| symbol.name == name && symbol.scope.is_none())
            .filter(|symbol| {
                symbol.module_key == doc.module_key
                    || symbol.kind == SymbolKind::Module
                    || symbol.uri == doc.uri && symbol.byte_start <= offset
            })
            .max_by_key(|symbol| {
                (
                    usize::from(symbol.uri == doc.uri),
                    usize::from(symbol.module_key == doc.module_key),
                    symbol.byte_start,
                )
            })
    }

    fn symbol_for_import_path<'a>(
        &'a self,
        doc: &IndexedDocument,
        path: &[String],
    ) -> Option<&'a NavSymbol> {
        let item = path.last()?;
        let module_path = &path[..path.len().saturating_sub(1)];
        let module_keys = project_context_for_uri(&doc.uri)
            .map(|project| project.imported_module_keys(&doc.module_key, module_path))
            .unwrap_or_else(|| fallback_imported_module_keys(&doc.module_key, module_path));
        self.symbols.iter().find(|symbol| {
            symbol.scope.is_none()
                && module_keys.contains(&symbol.module_key)
                && (symbol.name == *item || symbol.name.ends_with(&format!(".{item}")))
        })
    }

    fn module_for_path<'a>(&'a self, path: &[String]) -> Option<&'a NavSymbol> {
        self.symbols.iter().find(|symbol| {
            symbol.kind == SymbolKind::Module
                && symbol
                    .imported_path
                    .as_ref()
                    .is_some_and(|module| module == path)
        })
    }

    fn builtin_symbol<'a>(&'a self, doc: &IndexedDocument, name: &str) -> Option<&'a NavSymbol> {
        if !BUILTIN_CONSTRAINT_NAMES.contains(&name) {
            return None;
        }
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name && symbol.uri == doc.uri)
    }

    pub(super) fn references_to(
        &self,
        target: &NavSymbol,
        include_declaration: bool,
    ) -> Vec<lsp::Location> {
        let mut locations = Vec::new();
        if include_declaration && target.range != lsp::Range::default() {
            locations.push(lsp::Location {
                uri: target.uri.clone(),
                range: target.range,
            });
        }

        for doc in &self.docs {
            for (token_index, token) in doc.tokens.iter().enumerate() {
                if !matches!(token.token, Token::Ident(_)) {
                    continue;
                }
                let reference = Reference {
                    name: doc.reference_name(token_index),
                    offset: token.span.start,
                    use_path: doc
                        .use_path_at(token_index)
                        .or_else(|| doc.qualified_path_at(token_index)),
                };
                let Some(resolved) = self.resolve_reference(doc, &reference) else {
                    continue;
                };
                if same_symbol(resolved, target) {
                    locations.push(lsp::Location {
                        uri: doc.uri.clone(),
                        range: doc.span_to_range(token.span.clone()),
                    });
                }
            }
        }

        locations.sort_by(|a, b| {
            (
                a.uri.as_str(),
                a.range.start.line,
                a.range.start.character,
                a.range.end.line,
                a.range.end.character,
            )
                .cmp(&(
                    b.uri.as_str(),
                    b.range.start.line,
                    b.range.start.character,
                    b.range.end.line,
                    b.range.end.character,
                ))
        });
        locations.dedup_by(|a, b| {
            a.uri == b.uri && a.range.start == b.range.start && a.range.end == b.range.end
        });
        locations
    }
}
