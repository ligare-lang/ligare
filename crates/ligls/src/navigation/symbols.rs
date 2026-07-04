use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::core::syntax::Term;
use ligare::front::lexer::Token;
use ligare::front::parser::TopLevel;
use tower_lsp::lsp_types as lsp;

use super::{
    IndexedDocument, NavSymbol, Scope, SymbolKind, TokenSpan, doc_comment_before, unwrap_public,
};
use crate::completion::{
    Constraint, META_EXPR_TYPE, META_EXPR_VARIANTS, Signature, constructor_signature,
    signature_from_parts, term_signature, top_params, type_or_value_kind,
};

impl IndexedDocument {
    pub(super) fn collect_symbols<'bump>(
        &mut self,
        top_ranges: &[(usize, usize, TopLevel<'bump>)],
    ) {
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
                self.collect_type_members(name, body, start, end);
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
                    self.imports.push(super::ImportRef {
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
}
