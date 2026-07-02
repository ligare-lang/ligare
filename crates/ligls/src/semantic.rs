use std::collections::{HashMap, HashSet};
use std::ops::Range;

use ligare::core::syntax::{Term, Universe};
use ligare::front::lexer::Token;
use ligare::front::parser::{TopLevel, Visibility};
use tower_lsp::lsp_types as lsp;

use crate::completion::{TokenSpan, tokenize, top_level_ranges};
use crate::text::offset_to_position;
use crate::{Ast, parse_program_lsp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SemanticKind {
    Function,
    Variable,
    Constructor,
    Constraint,
    Namespace,
    Keyword,
    Parameter,
}

impl SemanticKind {
    #[cfg(test)]
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            SemanticKind::Function => "function",
            SemanticKind::Variable => "variable",
            SemanticKind::Constructor => "constructor",
            SemanticKind::Constraint => "constraint",
            SemanticKind::Namespace => "namespace",
            SemanticKind::Keyword => "keyword",
            SemanticKind::Parameter => "parameter",
        }
    }

    fn token_type(self) -> u32 {
        match self {
            SemanticKind::Function => 0,
            SemanticKind::Variable => 1,
            SemanticKind::Constructor => 2,
            SemanticKind::Constraint => 3,
            SemanticKind::Namespace => 4,
            SemanticKind::Keyword => 5,
            SemanticKind::Parameter => 6,
        }
    }
}

const MOD_DEFINITION: u32 = 1 << 0;
const MOD_PUBLIC: u32 = 1 << 1;

const BUILTIN_CONSTRAINTS: &[&str] = &[
    "int", "bool", "str", "IO", "Unit", "data", "prop", "theorem", "proof", "and", "or", "not",
    "implies", "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "c_int", "c_uint",
];

pub fn semantic_tokens_legend() -> lsp::SemanticTokensLegend {
    lsp::SemanticTokensLegend {
        token_types: vec![
            lsp::SemanticTokenType::FUNCTION,
            lsp::SemanticTokenType::VARIABLE,
            lsp::SemanticTokenType::new("constructor"),
            lsp::SemanticTokenType::new("constraint"),
            lsp::SemanticTokenType::NAMESPACE,
            lsp::SemanticTokenType::KEYWORD,
            lsp::SemanticTokenType::PARAMETER,
        ],
        token_modifiers: vec![
            lsp::SemanticTokenModifier::DEFINITION,
            lsp::SemanticTokenModifier::new("public"),
        ],
    }
}

pub(crate) fn semantic_tokens_for_source<'bump>(
    source: &str,
    ast: &Ast<'bump>,
    top_ranges: &[(usize, usize, TopLevel<'bump>)],
) -> Vec<lsp::SemanticToken> {
    let tokens = tokenize(source);
    let model = SemanticModel::build(top_ranges, &tokens);
    encode_tokens(
        source,
        collect_raw_tokens(source, ast, top_ranges, &tokens, &model),
    )
}

pub fn semantic_tokens_for_source_text(source: &str) -> lsp::SemanticTokens {
    let bump = bumpalo::Bump::new();
    let arena = ligare::core::pool::TermArena::new(&bump);
    let (ast, _) = parse_program_lsp(source, &bump, &arena);
    let top_ranges = top_level_ranges(source, &ast);
    lsp::SemanticTokens {
        result_id: None,
        data: semantic_tokens_for_source(source, &ast, &top_ranges),
    }
}

#[derive(Debug, Clone)]
struct RawSemanticToken {
    span: Range<usize>,
    kind: SemanticKind,
    modifiers: u32,
    priority: u8,
}

#[derive(Debug, Default)]
struct SemanticModel {
    functions: HashSet<String>,
    variables: HashSet<String>,
    constructors: HashSet<String>,
    constraints: HashSet<String>,
    namespaces: HashSet<String>,
    declarations: HashMap<usize, (SemanticKind, u32)>,
    locals: Vec<LocalScope>,
}

#[derive(Debug)]
struct LocalScope {
    range: Range<usize>,
    params: HashSet<String>,
    variables: HashSet<String>,
}

impl SemanticModel {
    fn build(top_ranges: &[(usize, usize, TopLevel<'_>)], tokens: &[TokenSpan]) -> Self {
        let mut model = Self::default();
        model
            .constraints
            .extend(BUILTIN_CONSTRAINTS.iter().map(|name| (*name).to_string()));

        for (start, end, top) in top_ranges {
            let (is_public, top) = unwrap_public(top);
            let modifiers = MOD_DEFINITION | u32::from(is_public) * MOD_PUBLIC;
            let range = *start..*end;
            let mut scope = LocalScope {
                range: range.clone(),
                params: HashSet::new(),
                variables: HashSet::new(),
            };

            match top {
                TopLevel::TLDef(name, params, ret, body, _) => {
                    let kind = definition_kind(params, *ret, body);
                    model.insert_named_definition(name, kind);
                    model.mark_declaration(tokens, &range, name, kind, modifiers);
                    model.collect_params(tokens, &range, params, &mut scope);
                    collect_type_members(body, &mut model);
                }
                TopLevel::TLExternDef(name, params, _, _) => {
                    model.functions.insert((*name).to_string());
                    model.mark_declaration(tokens, &range, name, SemanticKind::Function, modifiers);
                    model.collect_params(tokens, &range, params, &mut scope);
                }
                TopLevel::TLTheorem(name, _, _, _) => {
                    model.variables.insert((*name).to_string());
                    model.mark_declaration(tokens, &range, name, SemanticKind::Variable, modifiers);
                }
                TopLevel::TLUse(uses, visibility, _) => {
                    let is_public = matches!(visibility, Visibility::Public) || is_public;
                    let modifiers = MOD_DEFINITION | u32::from(is_public) * MOD_PUBLIC;
                    for tree in *uses {
                        for part in tree.path {
                            model.namespaces.insert((*part).to_string());
                            model.mark_declaration(
                                tokens,
                                &range,
                                part,
                                SemanticKind::Namespace,
                                modifiers,
                            );
                        }
                        if let Some(alias) = tree.alias {
                            model.namespaces.insert(alias.to_string());
                            model.mark_declaration(
                                tokens,
                                &range,
                                alias,
                                SemanticKind::Namespace,
                                modifiers,
                            );
                        }
                    }
                }
                TopLevel::TLMod(name, _) => {
                    model.namespaces.insert((*name).to_string());
                    model.mark_declaration(
                        tokens,
                        &range,
                        name,
                        SemanticKind::Namespace,
                        modifiers,
                    );
                }
                TopLevel::TLCheck(..) | TopLevel::TLEval(..) | TopLevel::TLExpr(..) => {}
                TopLevel::TLPublic(_) => unreachable!(),
            }

            model.collect_lexical_bindings(tokens, &range, &mut scope);
            if !scope.params.is_empty() || !scope.variables.is_empty() {
                model.locals.push(scope);
            }
        }

        model
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
            | SemanticKind::Parameter => {}
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
        let names: HashSet<_> = params.iter().map(|(name, _)| (*name).to_string()).collect();
        scope.params.extend(names.iter().cloned());
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
            if left.token == Token::LParen && names.contains(candidate) {
                self.declarations
                    .insert(name.span.start, (SemanticKind::Parameter, MOD_DEFINITION));
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
                    if is_do_bind_name(tokens, idx, range) {
                        if let Token::Ident(name) = &token.token {
                            scope.variables.insert(name.clone());
                            self.declarations
                                .insert(token.span.start, (SemanticKind::Variable, MOD_DEFINITION));
                        }
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
        let mut idx = bar_idx + 2;
        while let Some(token) = tokens.get(idx) {
            if token.span.start < range.start || token.span.end > range.end {
                break;
            }
            if token.token == Token::FatArrow {
                break;
            }
            if let Token::Ident(name) = &token.token {
                scope.variables.insert(name.clone());
                self.declarations
                    .insert(token.span.start, (SemanticKind::Variable, MOD_DEFINITION));
            }
            idx += 1;
        }
    }

    fn local_kind_at(&self, name: &str, offset: usize) -> Option<SemanticKind> {
        self.locals
            .iter()
            .find(|scope| scope.range.start <= offset && offset <= scope.range.end)
            .and_then(|scope| {
                if scope.params.contains(name) {
                    Some(SemanticKind::Parameter)
                } else if scope.variables.contains(name) {
                    Some(SemanticKind::Variable)
                } else {
                    None
                }
            })
    }

    fn global_kind(&self, name: &str) -> Option<SemanticKind> {
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

fn collect_raw_tokens(
    source: &str,
    _ast: &Ast<'_>,
    _top_ranges: &[(usize, usize, TopLevel<'_>)],
    tokens: &[TokenSpan],
    model: &SemanticModel,
) -> Vec<RawSemanticToken> {
    let mut raw = Vec::new();
    for (idx, token) in tokens.iter().enumerate() {
        if is_keyword(&token.token) {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind: SemanticKind::Keyword,
                modifiers: 0,
                priority: 1,
            });
        }

        let Token::Ident(name) = &token.token else {
            continue;
        };

        if let Some((kind, modifiers)) = model.declarations.get(&token.span.start) {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind: *kind,
                modifiers: *modifiers,
                priority: 10,
            });
            continue;
        }

        let kind = if is_use_path_token(tokens, idx) {
            Some(SemanticKind::Namespace)
        } else if let Some(kind) = dotted_kind(tokens, idx, model) {
            Some(kind)
        } else {
            model
                .local_kind_at(name, token.span.start)
                .or_else(|| model.global_kind(name))
        };

        if let Some(kind) = kind {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind,
                modifiers: 0,
                priority: 5,
            });
        } else if source[token.span.clone()].chars().next().is_some() {
            // Unknown identifiers intentionally remain unmarked.
        }
    }
    raw
}

fn encode_tokens(source: &str, raw: Vec<RawSemanticToken>) -> Vec<lsp::SemanticToken> {
    let mut by_start = HashMap::<usize, RawSemanticToken>::new();
    for token in raw {
        if token.span.is_empty() {
            continue;
        }
        match by_start.get(&token.span.start) {
            Some(existing) if existing.priority > token.priority => {}
            _ => {
                by_start.insert(token.span.start, token);
            }
        }
    }

    let mut positioned = by_start
        .into_values()
        .filter_map(|token| {
            let start = offset_to_position(source, token.span.start);
            let end = offset_to_position(source, token.span.end);
            (start.line == end.line && end.character >= start.character).then_some((
                start.line,
                start.character,
                end.character - start.character,
                token.kind,
                token.modifiers,
            ))
        })
        .collect::<Vec<_>>();
    positioned.sort_by_key(|(line, character, _, _, _)| (*line, *character));

    let mut previous_line = 0;
    let mut previous_start = 0;
    positioned
        .into_iter()
        .map(|(line, start, length, kind, modifiers)| {
            let delta_line = line - previous_line;
            let delta_start = if delta_line == 0 {
                start - previous_start
            } else {
                start
            };
            previous_line = line;
            previous_start = start;
            lsp::SemanticToken {
                delta_line,
                delta_start,
                length,
                token_type: kind.token_type(),
                token_modifiers_bitset: modifiers,
            }
        })
        .collect()
}

fn definition_kind(
    params: &[(ligare::core::syntax::Name<'_>, Option<&Term<'_>>)],
    ret: Option<&Term<'_>>,
    body: &Term<'_>,
) -> SemanticKind {
    if !params.is_empty() || ret.is_some_and(is_function_constraint) || is_function_value(body) {
        return SemanticKind::Function;
    }
    if is_constraint_definition(body) || ret.is_some_and(is_constraint_definition) {
        SemanticKind::Constraint
    } else {
        SemanticKind::Variable
    }
}

fn is_function_value(term: &Term<'_>) -> bool {
    match term {
        Term::Annot(inner, constraint) => {
            is_function_value(inner) || is_function_constraint(constraint)
        }
        Term::Lam(_) | Term::NamedLam(..) | Term::Pi(..) => true,
        _ => false,
    }
}

fn is_function_constraint(term: &Term<'_>) -> bool {
    matches!(term, Term::Pi(..))
}

fn is_constraint_definition(term: &Term<'_>) -> bool {
    match term {
        Term::Annot(inner, constraint) => {
            is_constraint_definition(inner) || matches!(constraint, Term::Universe(Universe::UProp))
        }
        Term::UnionDef(..)
        | Term::StructDef(..)
        | Term::Refine(..)
        | Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
        Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
            matches!(*name, "prop" | "theorem" | "proof")
        }
        _ => false,
    }
}

fn collect_type_members(term: &Term<'_>, model: &mut SemanticModel) {
    let inner = match term {
        Term::Annot(inner, _) => *inner,
        other => other,
    };
    match inner {
        Term::UnionDef(_, variants) => {
            for (variant, _) in *variants {
                model.constructors.insert((*variant).to_string());
            }
        }
        Term::StructDef(name, fields) => {
            model.constructors.insert(format!("{name}.mk"));
            model.constructors.insert("mk".to_string());
            for (field, _) in *fields {
                model.functions.insert(format!("{name}.{field}"));
                model.functions.insert((*field).to_string());
            }
        }
        _ => {}
    }
}

fn dotted_kind(tokens: &[TokenSpan], idx: usize, model: &SemanticModel) -> Option<SemanticKind> {
    let token = tokens.get(idx)?;
    let Token::Ident(name) = &token.token else {
        return None;
    };
    if tokens
        .get(idx + 1)
        .is_some_and(|token| token.token == Token::Dot)
    {
        return model.global_kind(name).or(Some(SemanticKind::Constraint));
    }
    if idx >= 2 && tokens[idx - 1].token == Token::Dot {
        let Token::Ident(parent) = &tokens[idx - 2].token else {
            return model.global_kind(name);
        };
        let dotted = format!("{parent}.{name}");
        if model.constructors.contains(&dotted) || model.constructors.contains(name) {
            Some(SemanticKind::Constructor)
        } else if model.functions.contains(&dotted) {
            Some(SemanticKind::Function)
        } else {
            model.global_kind(name)
        }
    } else {
        None
    }
}

fn ident_after(tokens: &[TokenSpan], idx: usize) -> Option<(String, Range<usize>)> {
    tokens.get(idx + 1).and_then(|token| match &token.token {
        Token::Ident(name) => Some((name.clone(), token.span.clone())),
        _ => None,
    })
}

fn is_do_bind_name(tokens: &[TokenSpan], idx: usize, range: &Range<usize>) -> bool {
    matches!(
        tokens.get(idx).map(|token| &token.token),
        Some(Token::Ident(_))
    ) && tokens
        .get(idx + 1)
        .is_some_and(|token| token.token == Token::LeftArrow)
        && tokens
            .get(idx)
            .is_some_and(|token| range.start <= token.span.start && token.span.end <= range.end)
}

fn is_use_path_token(tokens: &[TokenSpan], idx: usize) -> bool {
    let Some(token) = tokens.get(idx) else {
        return false;
    };
    if !matches!(token.token, Token::Ident(_)) {
        return false;
    }
    let mut i = idx;
    while i > 0
        && matches!(
            tokens[i - 1].token,
            Token::PathSep | Token::Ident(_) | Token::Comma | Token::LBrace | Token::RBrace
        )
    {
        i -= 1;
    }
    i > 0 && tokens[i - 1].token == Token::KwUse
}

fn is_keyword(token: &Token) -> bool {
    matches!(
        token,
        Token::KwLet
            | Token::KwIn
            | Token::KwIf
            | Token::KwThen
            | Token::KwElse
            | Token::True
            | Token::False
            | Token::KwBy
            | Token::KwFun
            | Token::KwFunc
            | Token::KwDo
            | Token::KwWhere
            | Token::KwDef
            | Token::KwExtern
            | Token::KwUnsafe
            | Token::KwAuto
            | Token::KwExact
            | Token::KwApply
            | Token::KwIntro
            | Token::KwHave
            | Token::KwTheorem
            | Token::KwPub
            | Token::KwUse
            | Token::KwMod
            | Token::KwAs
            | Token::KwStruct
            | Token::KwUnion
            | Token::KwMatch
            | Token::KwWith
            | Token::KwOf
            | Token::HashCheck
            | Token::HashEval
    )
}

fn unwrap_public<'a, 'bump>(top: &'a TopLevel<'bump>) -> (bool, &'a TopLevel<'bump>) {
    match top {
        TopLevel::TLPublic(inner) => (true, inner),
        other => (false, other),
    }
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DecodedSemanticToken {
    pub(crate) text: String,
    pub(crate) kind: &'static str,
    pub(crate) modifiers: Vec<&'static str>,
}

#[cfg(test)]
pub(crate) fn decode_semantic_tokens(
    source: &str,
    tokens: &[lsp::SemanticToken],
) -> Vec<DecodedSemanticToken> {
    let mut line = 0;
    let mut character = 0;
    tokens
        .iter()
        .filter_map(|token| {
            line += token.delta_line;
            character = if token.delta_line == 0 {
                character + token.delta_start
            } else {
                token.delta_start
            };
            let start = crate::text::position_to_offset(source, lsp::Position { line, character })?;
            let end = crate::text::position_to_offset(
                source,
                lsp::Position {
                    line,
                    character: character + token.length,
                },
            )?;
            Some(DecodedSemanticToken {
                text: source[start..end].to_string(),
                kind: token_kind_name(token.token_type),
                modifiers: token_modifiers(token.token_modifiers_bitset),
            })
        })
        .collect()
}

#[cfg(test)]
fn token_kind_name(idx: u32) -> &'static str {
    match idx {
        0 => SemanticKind::Function.as_str(),
        1 => SemanticKind::Variable.as_str(),
        2 => SemanticKind::Constructor.as_str(),
        3 => SemanticKind::Constraint.as_str(),
        4 => SemanticKind::Namespace.as_str(),
        5 => SemanticKind::Keyword.as_str(),
        6 => SemanticKind::Parameter.as_str(),
        _ => "unknown",
    }
}

#[cfg(test)]
fn token_modifiers(bitset: u32) -> Vec<&'static str> {
    let mut modifiers = Vec::new();
    if bitset & MOD_DEFINITION != 0 {
        modifiers.push("definition");
    }
    if bitset & MOD_PUBLIC != 0 {
        modifiers.push("public");
    }
    modifiers
}
