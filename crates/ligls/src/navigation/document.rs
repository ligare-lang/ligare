use bumpalo::Bump;
use ligare::core::pool::TermArena;
use ligare::front::lexer::Token;
use tower_lsp::lsp_types as lsp;

use super::{IndexedDocument, Reference, SourceDocument, TokenSpan};
use crate::completion::{expanded_top_level_ranges, tokenize};
use crate::document::{offset_to_position, position_to_offset};
use crate::parse_program_lsp;
use crate::workspace::{ProjectContext, fallback_module_key};

impl IndexedDocument {
    pub(super) fn build(document: &SourceDocument, project: Option<&ProjectContext>) -> Self {
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

    pub(super) fn reference_at(&self, position: lsp::Position) -> Option<Reference> {
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

    pub(super) fn reference_name(&self, token_index: usize) -> String {
        let Token::Ident(name) = &self.tokens[token_index].token else {
            return String::new();
        };

        if token_index >= 2 && self.tokens[token_index - 1].token == Token::Dot {
            let parent = self
                .qualified_path_at(token_index - 2)
                .map(|parts| parts.join("::"))
                .or_else(|| match &self.tokens[token_index - 2].token {
                    Token::Ident(parent) => Some(parent.clone()),
                    _ => None,
                })
                .unwrap_or_default();
            if !parent.is_empty() {
                return format!("{parent}.{name}");
            }
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
            let parent = self
                .qualified_path_at(token_index)
                .map(|parts| parts.join("::"))
                .unwrap_or_else(|| name.clone());
            return format!("{parent}.{child}");
        }

        name.clone()
    }

    pub(super) fn use_path_at(&self, token_index: usize) -> Option<Vec<String>> {
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

    pub(super) fn qualified_path_at(&self, token_index: usize) -> Option<Vec<String>> {
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

    pub(super) fn import_for_name(&self, name: &str) -> Option<Vec<String>> {
        for import in &self.imports {
            if import.name == name {
                return Some(import.path.clone());
            }
        }
        None
    }

    pub(super) fn span_to_range(&self, span: std::ops::Range<usize>) -> lsp::Range {
        lsp::Range {
            start: offset_to_position(&self.text, span.start),
            end: offset_to_position(&self.text, span.end),
        }
    }
}
