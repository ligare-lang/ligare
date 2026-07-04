use std::collections::HashSet;
use std::ops::Range;

use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::core::syntax::Term;
use ligare::front::lexer::Token;
use ligare::front::parser::{TopLevel, Visibility};

use super::{LocalScope, MOD_DEFINITION, MOD_PUBLIC, SemanticKind, SemanticModel, TokenSpan};
use crate::completion::{META_EXPR_TYPE, META_EXPR_VARIANTS};
use crate::semantic::classify::{
    collect_constraint_names, collect_type_members, definition_kind, ident_after, is_do_bind_name,
    is_type_parameter_constraint, namespace_item_ranges, qualified_name, unwrap_public,
};

impl SemanticModel {
    pub(super) fn build(top_ranges: &[(usize, usize, TopLevel<'_>)], tokens: &[TokenSpan]) -> Self {
        let mut model = Self::default();
        model.constraints.extend(
            BUILTIN_CONSTRAINT_NAMES
                .iter()
                .map(|name| (*name).to_string()),
        );
        model.constraints.insert(META_EXPR_TYPE.to_string());
        model
            .constructors
            .extend(META_EXPR_VARIANTS.iter().map(|name| (*name).to_string()));

        for (start, end, top) in top_ranges {
            model.collect_top(tokens, &(*start..*end), top, None);
        }

        model
    }

    fn collect_top(
        &mut self,
        tokens: &[TokenSpan],
        range: &Range<usize>,
        top: &TopLevel<'_>,
        namespace: Option<&str>,
    ) {
        let (is_public, top) = unwrap_public(top);
        let modifiers = MOD_DEFINITION | (u32::from(is_public) * MOD_PUBLIC);
        let mut scope = LocalScope {
            range: range.clone(),
            constraints: HashSet::new(),
            params: HashSet::new(),
            variables: HashSet::new(),
        };

        match top {
            TopLevel::TLDef(name, params, ret, body, _) => {
                let kind = definition_kind(params, *ret, body);
                let qualified = qualified_name(namespace, name);
                self.insert_named_definition(&qualified, kind);
                self.mark_declaration(tokens, range, name, kind, modifiers);
                self.collect_params(tokens, range, params, &mut scope);
                collect_type_members(name, &qualified, body, self);
            }
            TopLevel::TLExternDef(name, params, _, _) => {
                let qualified = qualified_name(namespace, name);
                self.functions.insert(qualified);
                self.mark_declaration(tokens, range, name, SemanticKind::Function, modifiers);
                self.collect_params(tokens, range, params, &mut scope);
            }
            TopLevel::TLInstance(name, constraint, _, _) => {
                let qualified = qualified_name(namespace, name);
                self.variables.insert(qualified);
                self.mark_declaration(tokens, range, name, SemanticKind::Variable, modifiers);
                collect_constraint_names(constraint, &mut self.constraints);
            }
            TopLevel::TLVariable(params, _) => {
                self.collect_params(tokens, range, params, &mut scope);
            }
            TopLevel::TLTheorem(name, _, _, _) => {
                let qualified = qualified_name(namespace, name);
                self.variables.insert(qualified);
                self.mark_declaration(tokens, range, name, SemanticKind::Variable, modifiers);
            }
            TopLevel::TLUse(uses, visibility, _) => {
                let is_public = matches!(visibility, Visibility::Public) || is_public;
                let modifiers = MOD_DEFINITION | (u32::from(is_public) * MOD_PUBLIC);
                for tree in *uses {
                    for part in tree.path {
                        self.namespaces.insert((*part).to_string());
                        self.mark_declaration(
                            tokens,
                            range,
                            part,
                            SemanticKind::Namespace,
                            modifiers,
                        );
                    }
                    if let Some(alias) = tree.alias {
                        self.namespaces.insert(alias.to_string());
                        self.mark_declaration(
                            tokens,
                            range,
                            alias,
                            SemanticKind::Namespace,
                            modifiers,
                        );
                    }
                }
            }
            TopLevel::TLMod(name, _) => {
                self.namespaces.insert((*name).to_string());
                self.mark_declaration(tokens, range, name, SemanticKind::Namespace, modifiers);
            }
            TopLevel::TLNamespace(name, items, _) => {
                let qualified = qualified_name(namespace, name);
                self.namespaces.insert((*name).to_string());
                self.namespaces.insert(qualified.clone());
                self.mark_declaration(tokens, range, name, SemanticKind::Namespace, modifiers);

                for (item_range, item) in namespace_item_ranges(items, range) {
                    self.collect_top(tokens, &item_range, item, Some(&qualified));
                }
                return;
            }
            TopLevel::TLCheck(..)
            | TopLevel::TLEval(..)
            | TopLevel::TLExpr(..)
            | TopLevel::TLSplice(..) => {}
            TopLevel::TLPublic(_) | TopLevel::TLAttributed(..) => unreachable!(),
        }

        self.collect_lexical_bindings(tokens, range, &mut scope);
        if !scope.constraints.is_empty() || !scope.params.is_empty() || !scope.variables.is_empty()
        {
            self.locals.push(scope);
        }
    }

    fn insert_named_definition(&mut self, name: &str, kind: SemanticKind) {
        match kind {
            SemanticKind::Function => {
                self.functions.insert(name.to_string());
            }
            SemanticKind::Variable => {
                self.variables.insert(name.to_string());
            }
            SemanticKind::Constraint => {
                self.constraints.insert(name.to_string());
            }
            SemanticKind::Constructor
            | SemanticKind::Namespace
            | SemanticKind::Keyword
            | SemanticKind::Parameter
            | SemanticKind::Comment
            | SemanticKind::Attribute => {}
        }
    }

    fn mark_declaration(
        &mut self,
        tokens: &[TokenSpan],
        range: &Range<usize>,
        name: &str,
        kind: SemanticKind,
        modifiers: u32,
    ) {
        if let Some(token) = tokens.iter().find(|token| {
            range.start <= token.span.start
                && token.span.end <= range.end
                && matches!(&token.token, Token::Ident(candidate) if candidate == name)
        }) {
            self.declarations
                .insert(token.span.start, (kind, modifiers));
        }
    }

    fn collect_params(
        &mut self,
        tokens: &[TokenSpan],
        range: &Range<usize>,
        params: &[(ligare::core::syntax::Name<'_>, Option<&Term<'_>>)],
        scope: &mut LocalScope,
    ) {
        let names: Vec<_> = params
            .iter()
            .map(|(name, constraint)| {
                (
                    (*name).to_string(),
                    constraint.is_some_and(is_type_parameter_constraint),
                )
            })
            .collect();
        for (name, is_type_param) in &names {
            if *is_type_param {
                scope.constraints.insert(name.clone());
            } else {
                scope.params.insert(name.clone());
            }
        }
        for window in tokens.windows(3) {
            let [left, name, right] = window else {
                continue;
            };
            if left.span.start < range.start || right.span.end > range.end {
                continue;
            }
            let Token::Ident(candidate) = &name.token else {
                continue;
            };
            if matches!(left.token, Token::LParen | Token::LBrace)
                && let Some((_, is_type_param)) = names.iter().find(|(name, _)| name == candidate)
            {
                let kind = if *is_type_param {
                    SemanticKind::Constraint
                } else {
                    SemanticKind::Parameter
                };
                self.declarations
                    .insert(name.span.start, (kind, MOD_DEFINITION));
            }
        }
    }

    fn collect_lexical_bindings(
        &mut self,
        tokens: &[TokenSpan],
        range: &Range<usize>,
        scope: &mut LocalScope,
    ) {
        for (idx, token) in tokens.iter().enumerate() {
            if token.span.start < range.start || token.span.end > range.end {
                continue;
            }
            match token.token {
                Token::KwLet => {
                    if let Some(name) = ident_after(tokens, idx) {
                        scope.variables.insert(name.0.clone());
                        self.declarations
                            .insert(name.1.start, (SemanticKind::Variable, MOD_DEFINITION));
                    }
                }
                Token::KwFun => {
                    if let Some(name) = ident_after(tokens, idx) {
                        scope.params.insert(name.0.clone());
                        self.declarations
                            .insert(name.1.start, (SemanticKind::Parameter, MOD_DEFINITION));
                    }
                }
                Token::Bar => {
                    self.collect_match_branch_binds(tokens, idx, range, scope);
                }
                _ => {
                    if is_do_bind_name(tokens, idx, range)
                        && let Token::Ident(name) = &token.token
                    {
                        scope.variables.insert(name.clone());
                        self.declarations
                            .insert(token.span.start, (SemanticKind::Variable, MOD_DEFINITION));
                    }
                }
            }
        }
    }

    fn collect_match_branch_binds(
        &mut self,
        tokens: &[TokenSpan],
        bar_idx: usize,
        range: &Range<usize>,
        scope: &mut LocalScope,
    ) {
        let Some(fat_arrow_idx) = tokens[bar_idx + 1..]
            .iter()
            .position(|token| {
                token.span.start >= range.start
                    && token.span.end <= range.end
                    && matches!(token.token, Token::FatArrow | Token::Bar)
            })
            .map(|relative| bar_idx + 1 + relative)
        else {
            return;
        };
        if tokens[fat_arrow_idx].token != Token::FatArrow {
            return;
        }

        for token in &tokens[bar_idx + 2..fat_arrow_idx] {
            if token.span.start < range.start || token.span.end > range.end {
                break;
            }
            if let Token::Ident(name) = &token.token {
                scope.variables.insert(name.clone());
                self.declarations
                    .insert(token.span.start, (SemanticKind::Variable, MOD_DEFINITION));
            }
        }
    }

    pub(super) fn local_kind_at(&self, name: &str, offset: usize) -> Option<SemanticKind> {
        self.locals
            .iter()
            .find(|scope| scope.range.start <= offset && offset <= scope.range.end)
            .and_then(|scope| {
                if scope.constraints.contains(name) {
                    Some(SemanticKind::Constraint)
                } else if scope.params.contains(name) {
                    Some(SemanticKind::Parameter)
                } else if scope.variables.contains(name) {
                    Some(SemanticKind::Variable)
                } else {
                    None
                }
            })
    }

    pub(super) fn global_kind(&self, name: &str) -> Option<SemanticKind> {
        if self.constructors.contains(name) {
            Some(SemanticKind::Constructor)
        } else if self.constraints.contains(name) {
            Some(SemanticKind::Constraint)
        } else if self.functions.contains(name) {
            Some(SemanticKind::Function)
        } else if self.variables.contains(name) {
            Some(SemanticKind::Variable)
        } else if self.namespaces.contains(name) {
            Some(SemanticKind::Namespace)
        } else {
            None
        }
    }
}
