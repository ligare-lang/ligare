use std::collections::{HashMap, HashSet};
use std::ops::Range;

use ligare::checker::builtin::BUILTIN_CONSTRAINT_NAMES;
use ligare::config::BUILTIN_UNIT;
use ligare::core::syntax::{Term, Universe};
use ligare::front::lexer::Token;
use ligare::front::parser::{TopLevel, Visibility};
use tower_lsp::lsp_types as lsp;

use crate::completion::{TokenSpan, tokenize, top_level_ranges, top_start};
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
    Comment,
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
            SemanticKind::Comment => "comment",
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
            SemanticKind::Comment => 7,
        }
    }
}

const MOD_DEFINITION: u32 = 1 << 0;
const MOD_PUBLIC: u32 = 1 << 1;

pub fn semantic_tokens_legend() -> lsp::SemanticTokensLegend {
    lsp::SemanticTokensLegend {
        token_types: vec![
            lsp::SemanticTokenType::FUNCTION,
            lsp::SemanticTokenType::VARIABLE,
            lsp::SemanticTokenType::new("constructor"),
            lsp::SemanticTokenType::TYPE,
            lsp::SemanticTokenType::NAMESPACE,
            lsp::SemanticTokenType::KEYWORD,
            lsp::SemanticTokenType::PARAMETER,
            lsp::SemanticTokenType::COMMENT,
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
    constraints: HashSet<String>,
    params: HashSet<String>,
    variables: HashSet<String>,
}

impl SemanticModel {
    fn build(top_ranges: &[(usize, usize, TopLevel<'_>)], tokens: &[TokenSpan]) -> Self {
        let mut model = Self::default();
        model.constraints.extend(
            BUILTIN_CONSTRAINT_NAMES
                .iter()
                .map(|name| (*name).to_string()),
        );

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
        let modifiers = MOD_DEFINITION | u32::from(is_public) * MOD_PUBLIC;
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
            TopLevel::TLTheorem(name, _, _, _) => {
                let qualified = qualified_name(namespace, name);
                self.variables.insert(qualified);
                self.mark_declaration(tokens, range, name, SemanticKind::Variable, modifiers);
            }
            TopLevel::TLUse(uses, visibility, _) => {
                let is_public = matches!(visibility, Visibility::Public) || is_public;
                let modifiers = MOD_DEFINITION | u32::from(is_public) * MOD_PUBLIC;
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
            TopLevel::TLCheck(..) | TopLevel::TLEval(..) | TopLevel::TLExpr(..) => {}
            TopLevel::TLPublic(_) => unreachable!(),
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
            | SemanticKind::Comment => {}
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

    fn local_kind_at(&self, name: &str, offset: usize) -> Option<SemanticKind> {
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
    let mut raw = comment_tokens(source);
    for (idx, token) in tokens.iter().enumerate() {
        if is_unit_builtin_token(tokens, idx) {
            raw.push(RawSemanticToken {
                span: token.span.start..tokens[idx + 1].span.end,
                kind: SemanticKind::Constraint,
                modifiers: 0,
                priority: 5,
            });
            continue;
        }

        if is_builtin_constraint_keyword(source, tokens, idx) {
            raw.push(RawSemanticToken {
                span: token.span.clone(),
                kind: SemanticKind::Constraint,
                modifiers: 0,
                priority: 5,
            });
            continue;
        }

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

        let kind = if let Some(kind) = qualified_path_kind(tokens, idx, model) {
            Some(kind)
        } else if is_use_path_token(tokens, idx) {
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

fn is_unit_builtin_token(tokens: &[TokenSpan], idx: usize) -> bool {
    tokens
        .get(idx)
        .is_some_and(|token| token.token == Token::LParen)
        && tokens
            .get(idx + 1)
            .is_some_and(|token| token.token == Token::RParen)
        && BUILTIN_CONSTRAINT_NAMES.contains(&BUILTIN_UNIT)
}

fn is_builtin_constraint_keyword(source: &str, tokens: &[TokenSpan], idx: usize) -> bool {
    let Some(token) = tokens.get(idx) else {
        return false;
    };
    token.token == Token::KwTheorem && !is_theorem_declaration_token(source, tokens, idx)
}

fn is_theorem_declaration_token(source: &str, tokens: &[TokenSpan], idx: usize) -> bool {
    let Some(token) = tokens.get(idx) else {
        return false;
    };
    if is_line_start(source, token.span.start) {
        return true;
    }
    previous_non_newline(tokens, idx)
        .is_some_and(|prev| prev.token == Token::KwPub && is_line_start(source, prev.span.start))
}

fn previous_non_newline(tokens: &[TokenSpan], idx: usize) -> Option<&TokenSpan> {
    tokens[..idx]
        .iter()
        .rev()
        .find(|token| token.token != Token::Newline)
}

fn is_line_start(source: &str, offset: usize) -> bool {
    source[..offset]
        .rsplit_once('\n')
        .map_or(offset == 0, |(_, line)| line.trim().is_empty())
}

fn comment_tokens(source: &str) -> Vec<RawSemanticToken> {
    let mut raw = Vec::new();
    let bytes = source.as_bytes();
    let mut index = 0;

    while index < bytes.len() {
        if starts_with(bytes, index, b"--") {
            let start = index;
            index += 2;
            while index < bytes.len() && bytes[index] != b'\n' {
                index += 1;
            }
            push_comment_span(source, start..index, &mut raw);
        } else if starts_with(bytes, index, b"{-") {
            let start = index;
            index = scan_block_comment(bytes, index + 2, b'-', b'}');
            push_comment_span(source, start..index, &mut raw);
        } else if starts_with(bytes, index, b"/-") {
            let start = index;
            index = scan_nestable_block_comment(bytes, index + 2);
            push_comment_span(source, start..index, &mut raw);
        } else if bytes[index] == b'"' {
            index = scan_string(bytes, index + 1);
        } else {
            index += 1;
        }
    }

    raw
}

fn starts_with(bytes: &[u8], index: usize, needle: &[u8]) -> bool {
    bytes
        .get(index..index + needle.len())
        .is_some_and(|slice| slice == needle)
}

fn scan_block_comment(bytes: &[u8], mut index: usize, close_first: u8, close_second: u8) -> usize {
    while index + 1 < bytes.len() {
        if bytes[index] == close_first && bytes[index + 1] == close_second {
            return index + 2;
        }
        index += 1;
    }
    bytes.len()
}

fn scan_nestable_block_comment(bytes: &[u8], mut index: usize) -> usize {
    let mut depth = 1u32;
    while index + 1 < bytes.len() {
        if bytes[index] == b'/' && bytes[index + 1] == b'-' {
            depth += 1;
            index += 2;
        } else if bytes[index] == b'-' && bytes[index + 1] == b'/' {
            depth -= 1;
            index += 2;
            if depth == 0 {
                return index;
            }
        } else {
            index += 1;
        }
    }
    bytes.len()
}

fn scan_string(bytes: &[u8], mut index: usize) -> usize {
    while index < bytes.len() {
        if bytes[index] == b'\\' {
            index = (index + 2).min(bytes.len());
        } else if bytes[index] == b'"' {
            return index + 1;
        } else {
            index += 1;
        }
    }
    bytes.len()
}

fn push_comment_span(source: &str, span: Range<usize>, raw: &mut Vec<RawSemanticToken>) {
    let mut start = span.start;
    while start < span.end {
        let line_end = source[start..span.end]
            .find('\n')
            .map_or(span.end, |relative| start + relative);
        let token_end = if line_end > start && source.as_bytes()[line_end - 1] == b'\r' {
            line_end - 1
        } else {
            line_end
        };
        if start < token_end {
            raw.push(RawSemanticToken {
                span: start..token_end,
                kind: SemanticKind::Comment,
                modifiers: 0,
                priority: 20,
            });
        }
        if line_end == span.end {
            break;
        }
        start = line_end + 1;
    }
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
    if is_constraint_definition(body) || ret.is_some_and(is_constraint_definition) {
        SemanticKind::Constraint
    } else if !params.is_empty()
        || ret.is_some_and(is_function_constraint)
        || is_function_value(body)
    {
        SemanticKind::Function
    } else {
        SemanticKind::Variable
    }
}

fn is_type_parameter_constraint(term: &Term<'_>) -> bool {
    match term {
        Term::Implicit(inner) => is_type_parameter_constraint(inner),
        Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
            matches!(*name, "prop" | "theorem" | "proof")
        }
        Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
        _ => false,
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

fn collect_constraint_names(term: &Term<'_>, constraints: &mut HashSet<String>) {
    match term {
        Term::Named(name) | Term::Global(name) | Term::Builtin(name) => {
            constraints.insert((*name).to_string());
        }
        Term::Implicit(inner) => collect_constraint_names(inner, constraints),
        Term::App(f, a) | Term::Annot(f, a) | Term::Pi(_, f, a) | Term::Refine(_, f, a) => {
            collect_constraint_names(f, constraints);
            collect_constraint_names(a, constraints);
        }
        _ => {}
    }
}

fn is_constraint_definition(term: &Term<'_>) -> bool {
    match term {
        Term::Annot(inner, constraint) => {
            is_constraint_definition(inner) || matches!(constraint, Term::Universe(Universe::UProp))
        }
        Term::EnumDef(..)
        | Term::StructDef(..)
        | Term::Refine(..)
        | Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof) => true,
        Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
            matches!(*name, "prop" | "theorem" | "proof")
        }
        _ => false,
    }
}

fn collect_type_members(
    _type_name: &str,
    qualified_type_name: &str,
    term: &Term<'_>,
    model: &mut SemanticModel,
) {
    let inner = match term {
        Term::Annot(inner, _) => *inner,
        other => other,
    };
    let namespace = qualified_type_name
        .rsplit_once("::")
        .map(|(namespace, _)| namespace);
    match inner {
        Term::EnumDef(_, variants) => {
            for (variant, _) in *variants {
                let name = namespace
                    .map(|namespace| format!("{namespace}::{variant}"))
                    .unwrap_or_else(|| (*variant).to_string());
                model.constructors.insert(name);
            }
        }
        Term::StructDef(_, fields) => {
            model
                .constructors
                .insert(format!("{qualified_type_name}.mk"));
            if namespace.is_none() {
                model.constructors.insert("mk".to_string());
            }
            for (field, _) in *fields {
                model
                    .functions
                    .insert(format!("{qualified_type_name}.{field}"));
                if namespace.is_none() {
                    model.functions.insert((*field).to_string());
                }
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
        let parent_path =
            qualified_path_ending_at(tokens, idx - 2).unwrap_or_else(|| parent.clone());
        let dotted = format!("{parent_path}.{name}");
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

fn qualified_path_kind(
    tokens: &[TokenSpan],
    idx: usize,
    model: &SemanticModel,
) -> Option<SemanticKind> {
    let path = qualified_path_at(tokens, idx)?;
    if path.parts.len() <= 1 {
        return None;
    }
    if path.part_index + 1 < path.parts.len() {
        return Some(SemanticKind::Namespace);
    }
    let name = path.parts[path.part_index].as_str();
    model
        .global_kind(&path.parts.join("::"))
        .or_else(|| model.global_kind(name))
}

struct QualifiedPath {
    parts: Vec<String>,
    part_index: usize,
}

fn qualified_path_at(tokens: &[TokenSpan], idx: usize) -> Option<QualifiedPath> {
    let Token::Ident(_) = tokens.get(idx)?.token else {
        return None;
    };

    let mut start = idx;
    while start >= 2
        && tokens[start - 1].token == Token::PathSep
        && matches!(tokens[start - 2].token, Token::Ident(_))
    {
        start -= 2;
    }

    let mut end = idx;
    while tokens
        .get(end + 1)
        .is_some_and(|token| token.token == Token::PathSep)
        && tokens
            .get(end + 2)
            .is_some_and(|token| matches!(token.token, Token::Ident(_)))
    {
        end += 2;
    }

    let mut parts = Vec::new();
    let mut part_index = None;
    let mut cursor = start;
    while cursor <= end {
        let Token::Ident(name) = &tokens[cursor].token else {
            return None;
        };
        if cursor == idx {
            part_index = Some(parts.len());
        }
        parts.push(name.clone());
        cursor += 2;
    }

    Some(QualifiedPath {
        parts,
        part_index: part_index?,
    })
}

fn qualified_path_ending_at(tokens: &[TokenSpan], idx: usize) -> Option<String> {
    let path = qualified_path_at(tokens, idx)?;
    (path.part_index + 1 == path.parts.len() && path.parts.len() > 1).then(|| path.parts.join("::"))
}

fn qualified_name(namespace: Option<&str>, name: &str) -> String {
    namespace
        .map(|namespace| format!("{namespace}::{name}"))
        .unwrap_or_else(|| name.to_string())
}

fn namespace_item_ranges<'a, 'bump>(
    items: &'a [TopLevel<'bump>],
    namespace_range: &Range<usize>,
) -> Vec<(Range<usize>, &'a TopLevel<'bump>)> {
    let mut starts: Vec<_> = items.iter().map(|item| (top_start(item), item)).collect();
    starts.sort_by_key(|(start, _)| *start);
    starts
        .iter()
        .enumerate()
        .map(|(idx, (start, item))| {
            let end = starts
                .get(idx + 1)
                .map(|(next, _)| *next)
                .unwrap_or(namespace_range.end);
            ((*start)..end, *item)
        })
        .collect()
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
            | Token::KwInstance
            | Token::KwUnsafe
            | Token::KwPure
            | Token::KwAuto
            | Token::KwExact
            | Token::KwApply
            | Token::KwIntro
            | Token::KwHave
            | Token::KwTheorem
            | Token::KwPub
            | Token::KwUse
            | Token::KwMod
            | Token::KwNamespace
            | Token::KwAs
            | Token::KwStruct
            | Token::KwEnum
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
        7 => SemanticKind::Comment.as_str(),
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
