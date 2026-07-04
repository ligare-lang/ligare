use std::ops::Range;

use bumpalo::Bump;
use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::core::pool::TermArena;
use ligare::core::syntax::Term;
use ligare::front::lexer::Token;
use ligare::front::parser::TopLevel;
use tower_lsp::lsp_types as lsp;

use crate::completion::{
    Constraint, META_EXPR_TYPE, META_EXPR_VARIANTS, Signature, SymbolKind, TokenSpan,
    constraint_from_source, constructor_signature, expanded_top_level_ranges,
    infer_literal_constraint, signature_from_parts, term_signature, tokenize, top_params,
    type_or_value_kind,
};
use crate::parse_program_lsp;
use crate::project::{
    ModuleKey, ProjectContext, fallback_imported_module_keys, fallback_module_key,
    project_context_for_uri,
};
use crate::text::{offset_to_position, position_to_offset};

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

#[derive(Debug, Clone)]
struct Reference {
    name: String,
    offset: usize,
    use_path: Option<Vec<String>>,
}

impl NavIndex {
    fn build(documents: &[SourceDocument], root_uri: &lsp::Url) -> Self {
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

    fn document(&self, uri: &lsp::Url) -> Option<&IndexedDocument> {
        self.docs.iter().find(|doc| &doc.uri == uri)
    }

    fn resolve_reference<'a>(
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

        if reference.name.contains('.') {
            if let Some(symbol) = self.visible_symbol(doc, &reference.name, reference.offset) {
                return Some(symbol);
            }
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
            .or_else(|| self.module_for_path(&[reference.name.clone()]))
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
                && module_keys
                    .iter()
                    .any(|module_key| symbol.module_key == *module_key)
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

    fn references_to(&self, target: &NavSymbol, include_declaration: bool) -> Vec<lsp::Location> {
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

impl IndexedDocument {
    fn build(document: &SourceDocument, project: Option<&ProjectContext>) -> Self {
        let bump = Bump::new();
        let arena = TermArena::new(&bump);
        let (ast, _) = parse_program_lsp(&document.text, &bump, &arena);
        let tokens = tokenize(&document.text);
        let top_ranges = expanded_top_level_ranges(&document.text, &ast, &bump, &arena);
        let module_key = project
            .map(|project| project.module_key_for_uri(&document.uri))
            .unwrap_or_else(|| fallback_module_key(&document.uri));

        let mut doc = Self {
            uri: document.uri.clone(),
            text: document.text.clone(),
            tokens,
            module_key,
            imports: Vec::new(),
            symbols: Vec::new(),
        };
        doc.collect_symbols(&top_ranges);
        doc
    }

    fn reference_at(&self, position: lsp::Position) -> Option<Reference> {
        let offset = position_to_offset(&self.text, position)?;
        let token_index = self.ident_token_at(offset)?;
        let name = self.reference_name(token_index);
        Some(Reference {
            name,
            offset,
            use_path: self
                .use_path_at(token_index)
                .or_else(|| self.qualified_path_at(token_index)),
        })
    }

    fn ident_token_at(&self, offset: usize) -> Option<usize> {
        self.tokens.iter().enumerate().find_map(|(idx, token)| {
            matches!(token.token, Token::Ident(_))
                .then_some(())
                .filter(|_| token.span.start <= offset && offset <= token.span.end)
                .map(|_| idx)
        })
    }

    fn reference_name(&self, token_index: usize) -> String {
        let Token::Ident(name) = &self.tokens[token_index].token else {
            return String::new();
        };

        if token_index >= 2
            && self.tokens[token_index - 1].token == Token::Dot
            && let Token::Ident(parent) = &self.tokens[token_index - 2].token
        {
            return format!("{parent}.{name}");
        }

        if self
            .tokens
            .get(token_index + 1)
            .is_some_and(|token| token.token == Token::Dot)
            && let Some(TokenSpan {
                token: Token::Ident(child),
                ..
            }) = self.tokens.get(token_index + 2)
        {
            return format!("{name}.{child}");
        }

        name.clone()
    }

    fn use_path_at(&self, token_index: usize) -> Option<Vec<String>> {
        let token = self.tokens.get(token_index)?;
        let Token::Ident(name) = &token.token else {
            return None;
        };

        for import in &self.imports {
            if !(import.start <= token.span.start && token.span.end <= import.end) {
                continue;
            }
            if import
                .alias_span
                .as_ref()
                .is_some_and(|span| span.start == token.span.start)
            {
                return Some(import.path.clone());
            }
            if let Some(index) = import.path.iter().position(|part| part == name) {
                return Some(import.path[..=index].to_vec());
            }
        }
        None
    }

    fn qualified_path_at(&self, token_index: usize) -> Option<Vec<String>> {
        if !matches!(self.tokens.get(token_index)?.token, Token::Ident(_)) {
            return None;
        }

        let mut start = token_index;
        while start >= 2
            && self.tokens[start - 1].token == Token::PathSep
            && matches!(self.tokens[start - 2].token, Token::Ident(_))
        {
            start -= 2;
        }

        let mut end = token_index;
        while self
            .tokens
            .get(end + 1)
            .is_some_and(|token| token.token == Token::PathSep)
            && self
                .tokens
                .get(end + 2)
                .is_some_and(|token| matches!(token.token, Token::Ident(_)))
        {
            end += 2;
        }

        if start == end {
            return None;
        }

        let parts = (start..=token_index)
            .step_by(2)
            .filter_map(|idx| match &self.tokens[idx].token {
                Token::Ident(part) => Some(part.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        (parts.len() > 1).then_some(parts)
    }

    fn import_for_name(&self, name: &str) -> Option<Vec<String>> {
        for import in &self.imports {
            if import.name == name {
                return Some(import.path.clone());
            }
        }
        None
    }

    fn collect_symbols<'bump>(&mut self, top_ranges: &[(usize, usize, TopLevel<'bump>)]) {
        for &(start, end, ref top) in top_ranges {
            self.collect_top_level_symbols(top, start, end);
            self.collect_local_symbols(top, start, end);
        }
        self.collect_builtin_symbols();
    }

    fn collect_top_level_symbols<'bump>(
        &mut self,
        top: &TopLevel<'bump>,
        start: usize,
        end: usize,
    ) {
        match unwrap_public(top) {
            TopLevel::TLDef(name, params, ret, body, _) => {
                let signature = if params.is_empty() {
                    term_signature(body)
                } else {
                    ret.map(|ret| signature_from_parts(params, ret))
                        .or_else(|| term_signature(body))
                };
                let constraint = signature
                    .as_ref()
                    .map(|sig| sig.whole.clone())
                    .or_else(|| ret.map(Constraint::from_term));
                let kind = if params.is_empty() {
                    type_or_value_kind(body)
                } else {
                    SymbolKind::Function
                };
                if let Some(span) = self.find_decl_name_span(start, end, name) {
                    self.push_symbol(NavSymbol {
                        name: (*name).to_string(),
                        detail: constraint
                            .as_ref()
                            .map(|c| c.display.clone())
                            .unwrap_or_else(|| "data".to_string()),
                        constraint,
                        signature,
                        kind,
                        uri: self.uri.clone(),
                        range: self.span_to_range(span.clone()),
                        byte_start: span.start,
                        module_key: self.module_key.clone(),
                        imported_path: None,
                        doc: doc_comment_before(&self.text, start),
                        scope: None,
                    });
                }
                self.collect_type_members(*name, body, start, end);
            }
            TopLevel::TLExternDef(name, params, ret, _) => {
                let signature = signature_from_parts(params, ret);
                if let Some(span) = self.find_decl_name_span(start, end, name) {
                    self.push_symbol(NavSymbol {
                        name: (*name).to_string(),
                        detail: signature.whole.display.clone(),
                        constraint: Some(signature.whole.clone()),
                        signature: Some(signature),
                        kind: SymbolKind::Function,
                        uri: self.uri.clone(),
                        range: self.span_to_range(span.clone()),
                        byte_start: span.start,
                        module_key: self.module_key.clone(),
                        imported_path: None,
                        doc: doc_comment_before(&self.text, start),
                        scope: None,
                    });
                }
            }
            TopLevel::TLInstance(name, constraint, _, _) => {
                if let Some(span) = self.find_decl_name_span(start, end, name) {
                    self.push_symbol(NavSymbol {
                        name: (*name).to_string(),
                        detail: ligare::pretty::PrettyPrinter::pretty(constraint),
                        constraint: Some(Constraint::from_term(constraint)),
                        signature: None,
                        kind: SymbolKind::Value,
                        uri: self.uri.clone(),
                        range: self.span_to_range(span.clone()),
                        byte_start: span.start,
                        module_key: self.module_key.clone(),
                        imported_path: None,
                        doc: doc_comment_before(&self.text, start),
                        scope: None,
                    });
                }
            }
            TopLevel::TLVariable(params, _) => {
                for (name, constraint) in *params {
                    if let Some(span) = self.find_param_span(start, end, name) {
                        self.push_symbol(NavSymbol {
                            name: (*name).to_string(),
                            detail: constraint
                                .map(|c| Constraint::from_term(c).display)
                                .unwrap_or_else(|| "data".to_string()),
                            constraint: constraint.map(Constraint::from_term),
                            signature: None,
                            kind: SymbolKind::Value,
                            uri: self.uri.clone(),
                            range: self.span_to_range(span.clone()),
                            byte_start: span.start,
                            module_key: self.module_key.clone(),
                            imported_path: None,
                            doc: None,
                            scope: Some(Scope {
                                uri: self.uri.clone(),
                                start,
                                end,
                            }),
                        });
                    }
                }
            }
            TopLevel::TLTheorem(name, prop, _, _) => {
                if let Some(span) = self.find_decl_name_span(start, end, name) {
                    self.push_symbol(NavSymbol {
                        name: (*name).to_string(),
                        detail: ligare::pretty::PrettyPrinter::pretty(prop),
                        constraint: Some(Constraint::from_term(prop)),
                        signature: None,
                        kind: SymbolKind::Value,
                        uri: self.uri.clone(),
                        range: self.span_to_range(span.clone()),
                        byte_start: span.start,
                        module_key: self.module_key.clone(),
                        imported_path: None,
                        doc: doc_comment_before(&self.text, start),
                        scope: None,
                    });
                }
            }
            TopLevel::TLUse(uses, _, _) => {
                for tree in *uses {
                    let path: Vec<String> =
                        tree.path.iter().map(|part| (*part).to_string()).collect();
                    let name = tree
                        .alias
                        .map(|alias| alias.to_string())
                        .or_else(|| path.last().cloned())
                        .unwrap_or_default();
                    let span = tree
                        .alias
                        .and_then(|alias| self.find_ident_span(start, end, alias))
                        .or_else(|| self.find_last_path_segment_span(start, end, &path));
                    self.imports.push(ImportRef {
                        path: path.clone(),
                        name: name.clone(),
                        alias_span: tree
                            .alias
                            .and_then(|alias| self.find_ident_span(start, end, alias)),
                        start,
                        end,
                    });
                    if !name.is_empty()
                        && let Some(span) = span
                    {
                        self.push_symbol(NavSymbol {
                            name,
                            detail: format!("import {}", path.join("::")),
                            constraint: None,
                            signature: None,
                            kind: SymbolKind::Import,
                            uri: self.uri.clone(),
                            range: self.span_to_range(span.clone()),
                            byte_start: span.start,
                            module_key: self.module_key.clone(),
                            imported_path: Some(path),
                            doc: None,
                            scope: None,
                        });
                    }
                }
            }
            TopLevel::TLMod(name, _) => {
                if let Some(span) = self.find_decl_name_span(start, end, name) {
                    let module_key = self.module_key.child((*name).to_string());
                    self.push_symbol(NavSymbol {
                        name: (*name).to_string(),
                        detail: "module".to_string(),
                        constraint: None,
                        signature: None,
                        kind: SymbolKind::Module,
                        uri: self.uri.clone(),
                        range: self.span_to_range(span.clone()),
                        byte_start: span.start,
                        module_key: self.module_key.clone(),
                        imported_path: Some(module_key.path),
                        doc: doc_comment_before(&self.text, start),
                        scope: None,
                    });
                }
            }
            TopLevel::TLNamespace(name, _, _) => {
                if let Some(span) = self.find_decl_name_span(start, end, name) {
                    self.push_symbol(NavSymbol {
                        name: (*name).to_string(),
                        detail: "namespace".to_string(),
                        constraint: None,
                        signature: None,
                        kind: SymbolKind::Module,
                        uri: self.uri.clone(),
                        range: self.span_to_range(span.clone()),
                        byte_start: span.start,
                        module_key: self.module_key.clone(),
                        imported_path: Some(vec![(*name).to_string()]),
                        doc: doc_comment_before(&self.text, start),
                        scope: None,
                    });
                }
            }
            TopLevel::TLCheck(_, _, _)
            | TopLevel::TLEval(_, _)
            | TopLevel::TLExpr(_, _)
            | TopLevel::TLSplice(_, _) => {}
            TopLevel::TLPublic(_) | TopLevel::TLAttributed(..) => unreachable!(),
        }
    }

    fn collect_type_members(&mut self, type_name: &str, body: &Term<'_>, start: usize, end: usize) {
        let inner = match body {
            Term::Annot(inner, _) => *inner,
            other => other,
        };
        match inner {
            Term::EnumDef(enum_name, variants) => {
                for (variant_name, fields) in *variants {
                    let signature = constructor_signature(enum_name, fields);
                    if let Some(span) = self.find_enum_variant_span(start, end, variant_name) {
                        self.push_symbol(NavSymbol {
                            name: (*variant_name).to_string(),
                            detail: signature
                                .as_ref()
                                .map(|sig| sig.whole.display.clone())
                                .unwrap_or_else(|| enum_name.to_string()),
                            constraint: signature
                                .as_ref()
                                .map(|sig| sig.whole.clone())
                                .or_else(|| Some(Constraint::named(enum_name))),
                            signature,
                            kind: SymbolKind::Constructor,
                            uri: self.uri.clone(),
                            range: self.span_to_range(span.clone()),
                            byte_start: span.start,
                            module_key: self.module_key.clone(),
                            imported_path: None,
                            doc: doc_comment_before(&self.text, span.start),
                            scope: None,
                        });
                    }
                }
            }
            Term::StructDef(struct_name, fields) => {
                if let Some(type_span) = self.find_decl_name_span(start, end, type_name) {
                    let ctor_signature = constructor_signature(struct_name, fields);
                    self.push_symbol(NavSymbol {
                        name: format!("{type_name}.mk"),
                        detail: ctor_signature
                            .as_ref()
                            .map(|sig| sig.whole.display.clone())
                            .unwrap_or_else(|| struct_name.to_string()),
                        constraint: ctor_signature
                            .as_ref()
                            .map(|sig| sig.whole.clone())
                            .or_else(|| Some(Constraint::named(struct_name))),
                        signature: ctor_signature,
                        kind: SymbolKind::Constructor,
                        uri: self.uri.clone(),
                        range: self.span_to_range(type_span.clone()),
                        byte_start: type_span.start,
                        module_key: self.module_key.clone(),
                        imported_path: None,
                        doc: doc_comment_before(&self.text, start),
                        scope: None,
                    });
                }
                for (field_name, field_constraint) in *fields {
                    if let Some(span) = self.find_struct_field_span(start, end, field_name) {
                        let whole = Constraint::new(format!(
                            "({} -> {})",
                            struct_name,
                            ligare::pretty::PrettyPrinter::pretty(field_constraint)
                        ));
                        self.push_symbol(NavSymbol {
                            name: format!("{type_name}.{field_name}"),
                            detail: whole.display.clone(),
                            constraint: Some(whole.clone()),
                            signature: Some(Signature {
                                whole,
                                params: vec![Constraint::named(struct_name)],
                                result: Constraint::from_term(field_constraint),
                            }),
                            kind: SymbolKind::Function,
                            uri: self.uri.clone(),
                            range: self.span_to_range(span.clone()),
                            byte_start: span.start,
                            module_key: self.module_key.clone(),
                            imported_path: None,
                            doc: doc_comment_before(&self.text, span.start),
                            scope: None,
                        });
                    }
                }
            }
            _ => {}
        }
    }

    fn collect_local_symbols<'bump>(&mut self, top: &TopLevel<'bump>, start: usize, end: usize) {
        let assign_end = self
            .tokens_between(start, end)
            .find(|token| token.token == Token::ColonEq)
            .map(|token| token.span.end)
            .unwrap_or(start);

        if let Some(params) = top_params(top) {
            for (name, constraint) in params {
                if let Some(span) = self.find_param_span(start, assign_end, name) {
                    let constraint = constraint
                        .map(Constraint::from_term)
                        .unwrap_or_else(|| Constraint::named("data"));
                    self.push_symbol(NavSymbol {
                        name: (*name).to_string(),
                        detail: constraint.display.clone(),
                        constraint: Some(constraint),
                        signature: None,
                        kind: SymbolKind::Local,
                        uri: self.uri.clone(),
                        range: self.span_to_range(span.clone()),
                        byte_start: span.start,
                        module_key: self.module_key.clone(),
                        imported_path: None,
                        doc: None,
                        scope: Some(Scope {
                            uri: self.uri.clone(),
                            start: assign_end,
                            end,
                        }),
                    });
                }
            }
        }

        let mut idx = 0;
        while idx + 1 < self.tokens.len() {
            let token = &self.tokens[idx];
            if token.span.start < assign_end
                || token.span.start >= end
                || token.token != Token::KwLet
            {
                idx += 1;
                continue;
            }
            let Some(TokenSpan {
                token: Token::Ident(name),
                span,
            }) = self.tokens.get(idx + 1)
            else {
                idx += 1;
                continue;
            };
            let constraint = self
                .let_constraint(idx, end)
                .unwrap_or_else(|| Constraint::named("data"));
            self.push_symbol(NavSymbol {
                name: name.clone(),
                detail: constraint.display.clone(),
                constraint: Some(constraint),
                signature: None,
                kind: SymbolKind::Local,
                uri: self.uri.clone(),
                range: self.span_to_range(span.clone()),
                byte_start: span.start,
                module_key: self.module_key.clone(),
                imported_path: None,
                doc: doc_comment_before(&self.text, token.span.start),
                scope: Some(Scope {
                    uri: self.uri.clone(),
                    start: span.end,
                    end,
                }),
            });
            idx += 1;
        }
    }

    fn collect_builtin_symbols(&mut self) {
        for name in BUILTIN_CONSTRAINT_NAMES {
            self.push_symbol(NavSymbol {
                name: (*name).to_string(),
                detail: "builtin constraint".to_string(),
                constraint: Some(Constraint::named("prop")),
                signature: None,
                kind: SymbolKind::Type,
                uri: self.uri.clone(),
                range: lsp::Range::default(),
                byte_start: 0,
                module_key: self.module_key.clone(),
                imported_path: None,
                doc: None,
                scope: None,
            });
        }
        self.push_symbol(NavSymbol {
            name: META_EXPR_TYPE.to_string(),
            detail: "builtin meta constraint".to_string(),
            constraint: Some(Constraint::named("prop")),
            signature: None,
            kind: SymbolKind::Type,
            uri: self.uri.clone(),
            range: lsp::Range::default(),
            byte_start: 0,
            module_key: self.module_key.clone(),
            imported_path: None,
            doc: None,
            scope: None,
        });
        for variant in META_EXPR_VARIANTS {
            self.push_symbol(NavSymbol {
                name: (*variant).to_string(),
                detail: META_EXPR_TYPE.to_string(),
                constraint: Some(Constraint::named(META_EXPR_TYPE)),
                signature: None,
                kind: SymbolKind::Constructor,
                uri: self.uri.clone(),
                range: lsp::Range::default(),
                byte_start: 0,
                module_key: self.module_key.clone(),
                imported_path: None,
                doc: None,
                scope: None,
            });
        }
    }

    fn push_symbol(&mut self, symbol: NavSymbol) {
        self.symbols.push(symbol);
    }

    fn tokens_between(&self, start: usize, end: usize) -> impl Iterator<Item = &TokenSpan> {
        self.tokens
            .iter()
            .filter(move |token| start <= token.span.start && token.span.end <= end)
    }

    fn find_decl_name_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        let mut after_header = false;
        for token in self.tokens_between(start, end) {
            match &token.token {
                Token::KwDef | Token::KwTheorem | Token::KwMod => after_header = true,
                Token::Ident(candidate) if after_header && candidate == name => {
                    return Some(token.span.clone());
                }
                Token::Newline if !after_header => {}
                _ => {}
            }
        }
        None
    }

    fn find_ident_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        self.tokens_between(start, end)
            .find_map(|token| match &token.token {
                Token::Ident(candidate) if candidate == name => Some(token.span.clone()),
                _ => None,
            })
    }

    fn find_last_path_segment_span(
        &self,
        start: usize,
        end: usize,
        path: &[String],
    ) -> Option<std::ops::Range<usize>> {
        let name = path.last()?;
        self.tokens_between(start, end)
            .filter_map(|token| match &token.token {
                Token::Ident(candidate) if candidate == name => Some(token.span.clone()),
                _ => None,
            })
            .last()
    }

    fn find_param_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        self.tokens_between(start, end)
            .collect::<Vec<_>>()
            .windows(2)
            .find_map(|window| {
                (window[0].token == Token::LParen)
                    .then_some(&window[1])
                    .and_then(|token| match &token.token {
                        Token::Ident(candidate) if candidate == name => Some(token.span.clone()),
                        _ => None,
                    })
            })
    }

    fn find_enum_variant_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        self.tokens_between(start, end)
            .collect::<Vec<_>>()
            .windows(2)
            .find_map(|window| {
                (window[0].token == Token::Bar)
                    .then_some(&window[1])
                    .and_then(|token| match &token.token {
                        Token::Ident(candidate) if candidate == name => Some(token.span.clone()),
                        _ => None,
                    })
            })
    }

    fn find_struct_field_span(
        &self,
        start: usize,
        end: usize,
        name: &str,
    ) -> Option<std::ops::Range<usize>> {
        let mut after_struct = false;
        let tokens: Vec<_> = self.tokens_between(start, end).collect();
        for window in tokens.windows(2) {
            if window[0].token == Token::KwStruct {
                after_struct = true;
                continue;
            }
            if after_struct
                && let Token::Ident(candidate) = &window[0].token
                && candidate == name
                && window[1].token == Token::Colon
            {
                return Some(window[0].span.clone());
            }
        }
        None
    }

    fn let_constraint(&self, let_idx: usize, end: usize) -> Option<Constraint> {
        let mut j = let_idx + 2;
        if self
            .tokens
            .get(j)
            .is_some_and(|token| token.token == Token::Colon)
        {
            let constraint_start = self.tokens[j].span.end;
            j += 1;
            while self.tokens.get(j).is_some_and(|token| {
                token.span.start < end
                    && !matches!(
                        token.token,
                        Token::ColonEq | Token::Eq | Token::KwIn | Token::Semi
                    )
            }) {
                j += 1;
            }
            if let Some(delim) = self.tokens.get(j) {
                return constraint_from_source(&self.text, constraint_start..delim.span.start);
            }
        }
        while self.tokens.get(j).is_some_and(|token| {
            token.span.start < end
                && !matches!(
                    token.token,
                    Token::ColonEq | Token::Eq | Token::KwIn | Token::Semi
                )
        }) {
            j += 1;
        }
        if self
            .tokens
            .get(j)
            .is_some_and(|token| matches!(token.token, Token::ColonEq | Token::Eq))
        {
            infer_literal_constraint(self.tokens.get(j + 1).map(|token| &token.token))
        } else {
            None
        }
    }

    fn span_to_range(&self, span: std::ops::Range<usize>) -> lsp::Range {
        lsp::Range {
            start: offset_to_position(&self.text, span.start),
            end: offset_to_position(&self.text, span.end),
        }
    }
}

impl NavSymbol {
    fn hover(&self) -> lsp::Hover {
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
    fn lsp_symbol_kind(self) -> lsp::SymbolKind {
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

fn same_symbol(left: &NavSymbol, right: &NavSymbol) -> bool {
    left.uri == right.uri
        && left.range.start == right.range.start
        && left.range.end == right.range.end
        && left.name == right.name
}

fn unwrap_public<'a, 'bump>(top: &'a TopLevel<'bump>) -> &'a TopLevel<'bump> {
    match top {
        TopLevel::TLPublic(inner) => unwrap_public(inner),
        TopLevel::TLAttributed(_, inner, _) => unwrap_public(inner),
        other => other,
    }
}

fn doc_comment_before(source: &str, start: usize) -> Option<String> {
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
