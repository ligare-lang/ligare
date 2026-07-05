use std::path::{Path, PathBuf};

use bumpalo::Bump;

use ligare::core::pool::TermArena;
use ligare::core::syntax::{DoStmt, Name, PrimOp, Tactic, Term};
use ligare::front::parser::{Attribute, ParseError, TopLevel, UseTree, Visibility, parse_program};

const INDENT: usize = 2;
const PREC_BLOCK: u8 = 0;
const PREC_ANNOT: u8 = 1;
const PREC_ARROW: u8 = 2;
const PREC_COMPARE: u8 = 3;
const PREC_ADD: u8 = 4;
const PREC_MUL: u8 = 5;
const PREC_APP: u8 = 6;
const PREC_ATOM: u8 = 7;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FormatReport {
    pub changed: Vec<PathBuf>,
}

pub fn format_source(source: &str) -> Result<String, ParseError> {
    let bump = Bump::new();
    let arena = TermArena::new(&bump);
    let tops = parse_program(source, &bump, &arena)?;
    Ok(SourceFormatter::new().format_top_levels(&tops))
}

pub fn format_path(path: &Path, check: bool) -> Result<FormatReport, String> {
    let files = collect_format_targets(path)
        .map_err(|err| format!("cannot read `{}`: {err}", path.display()))?;
    if files.is_empty() {
        return Err(format!("no .lig files found under `{}`", path.display()));
    }

    let mut report = FormatReport::default();
    let mut errors = Vec::new();

    for file in files {
        let source = match std::fs::read_to_string(&file) {
            Ok(source) => source,
            Err(err) => {
                errors.push(format!("cannot read `{}`: {err}", file.display()));
                continue;
            }
        };
        let formatted = match format_source(&source) {
            Ok(formatted) => formatted,
            Err(err) => {
                errors.push(format!("{}: {}", file.display(), err));
                continue;
            }
        };
        if source == formatted {
            continue;
        }
        report.changed.push(file.clone());
        if check {
            continue;
        }
        if let Err(err) = std::fs::write(&file, formatted) {
            errors.push(format!("cannot write `{}`: {err}", file.display()));
        }
    }

    if errors.is_empty() {
        Ok(report)
    } else {
        Err(errors.join("\n"))
    }
}

struct SourceFormatter;

struct TopMeta<'a, 'bump> {
    attrs: Vec<&'a Attribute<'bump>>,
    public: bool,
    inner: &'a TopLevel<'bump>,
}

#[derive(Clone, Copy)]
struct FunParam<'bump> {
    name: Name<'bump>,
    constraint: Option<&'bump Term<'bump>>,
    implicit: bool,
}

impl SourceFormatter {
    fn new() -> Self {
        Self
    }

    fn format_top_levels(&self, tops: &[TopLevel<'_>]) -> String {
        if tops.is_empty() {
            return String::new();
        }
        let body = tops
            .iter()
            .map(|top| self.format_top(top))
            .collect::<Vec<_>>()
            .join("\n\n");
        format!("{body}\n")
    }

    fn format_top(&self, top: &TopLevel<'_>) -> String {
        let meta = self.top_meta(top);
        let mut lines = meta
            .attrs
            .iter()
            .map(|attr| self.format_attr(attr))
            .collect::<Vec<_>>();
        let item = self.format_top_item(meta.inner, meta.public);
        if !item.is_empty() {
            lines.push(item);
        }
        lines.join("\n")
    }

    fn top_meta<'a, 'bump>(&self, mut top: &'a TopLevel<'bump>) -> TopMeta<'a, 'bump> {
        let mut attrs = Vec::new();
        let mut public = false;
        loop {
            match top {
                TopLevel::TLAttributed(item_attrs, inner, _) => {
                    attrs.extend(item_attrs.iter());
                    top = inner;
                }
                TopLevel::TLPublic(inner) => {
                    public = true;
                    top = inner;
                }
                inner => {
                    return TopMeta {
                        attrs,
                        public,
                        inner,
                    };
                }
            }
        }
    }

    fn format_top_item(&self, top: &TopLevel<'_>, public: bool) -> String {
        match top {
            TopLevel::TLDef(name, params, ret, body, _) => {
                let mut head = String::new();
                if public {
                    head.push_str("pub ");
                }
                head.push_str("def ");
                head.push_str(name);
                let params = self.format_decl_params(params);
                if !params.is_empty() {
                    head.push(' ');
                    head.push_str(&params);
                }
                if let Some(ret) = ret {
                    head.push_str(" : ");
                    head.push_str(&self.format_term(ret, PREC_BLOCK));
                }
                self.attach_body(head, body)
            }
            TopLevel::TLExternDef(name, params, ret, _) => {
                let mut out = String::new();
                if public {
                    out.push_str("pub ");
                }
                out.push_str("extern def ");
                out.push_str(name);
                let params = self.format_decl_params(params);
                if !params.is_empty() {
                    out.push(' ');
                    out.push_str(&params);
                }
                out.push_str(" : ");
                out.push_str(&self.format_term(ret, PREC_BLOCK));
                out
            }
            TopLevel::TLInstance(name, constraint, value, _) => {
                let mut head = String::new();
                if public {
                    head.push_str("pub ");
                }
                head.push_str("instance ");
                head.push_str(name);
                head.push_str(" : ");
                head.push_str(&self.format_term(constraint, PREC_BLOCK));
                self.attach_body(head, value)
            }
            TopLevel::TLVariable(params, _) => {
                let mut out = String::from("variable");
                let params = self.format_decl_params(params);
                if !params.is_empty() {
                    out.push(' ');
                    out.push_str(&params);
                }
                out
            }
            TopLevel::TLTheorem(name, prop, body, _) => {
                let mut head = String::new();
                if public {
                    head.push_str("pub ");
                }
                head.push_str("theorem ");
                head.push_str(name);
                head.push_str(" : ");
                head.push_str(&self.format_term(prop, PREC_BLOCK));
                self.attach_body(head, body)
            }
            TopLevel::TLUse(trees, visibility, _) => {
                let mut out = String::new();
                if matches!(visibility, Visibility::Public) || public {
                    out.push_str("pub ");
                }
                out.push_str("use ");
                out.push_str(
                    &trees
                        .iter()
                        .map(|tree| self.format_use_tree(tree))
                        .collect::<Vec<_>>()
                        .join(", "),
                );
                out
            }
            TopLevel::TLMod(name, _) => {
                if public {
                    format!("pub mod {name}")
                } else {
                    format!("mod {name}")
                }
            }
            TopLevel::TLNamespace(name, items, _) => self.format_namespace(name, items, public),
            TopLevel::TLCheck(term, constraint, _) => {
                let mut out = String::from("#check ");
                out.push_str(&self.format_term(term, PREC_BLOCK));
                out.push_str(" : ");
                out.push_str(&self.format_term(constraint, PREC_BLOCK));
                out
            }
            TopLevel::TLEval(term, _) => format!("#eval {}", self.format_term(term, PREC_BLOCK)),
            TopLevel::TLExpr(term, _) => self.format_term(term, PREC_BLOCK),
            TopLevel::TLSplice(term, _) => format!("$({})", self.format_term(term, PREC_BLOCK)),
            TopLevel::TLPublic(_) | TopLevel::TLAttributed(..) => String::new(),
        }
    }

    fn format_namespace(&self, name: &str, items: &[TopLevel<'_>], public: bool) -> String {
        let mut head = String::new();
        if public {
            head.push_str("pub ");
        }
        head.push_str("namespace ");
        head.push_str(name);
        if items.is_empty() {
            head.push_str(" {}");
            return head;
        }
        let body = items
            .iter()
            .map(|item| self.format_top(item))
            .collect::<Vec<_>>()
            .join("\n\n");
        format!("{head} {{\n{}\n}}", indent_block(&body, INDENT))
    }

    fn attach_body(&self, head: String, body: &Term<'_>) -> String {
        let body = self.format_term(body, PREC_BLOCK);
        if is_multiline(&body) {
            format!("{head} :=\n{}", indent_block(&body, INDENT))
        } else {
            format!("{head} := {body}")
        }
    }

    fn format_attr(&self, attr: &Attribute<'_>) -> String {
        let path = attr.path.join("::");
        if attr.args.is_empty() {
            return format!("#[{path}]");
        }
        let args = attr
            .args
            .iter()
            .map(|arg| self.format_term(arg, PREC_BLOCK))
            .collect::<Vec<_>>()
            .join(", ");
        format!("#[{path}({args})]")
    }

    fn format_use_tree(&self, tree: &UseTree<'_>) -> String {
        let mut out = tree.path.join("::");
        if tree.wildcard {
            out.push_str("::*");
        }
        if let Some(alias) = tree.alias {
            out.push_str(" as ");
            out.push_str(alias);
        }
        out
    }

    fn format_decl_params(&self, params: &[(Name<'_>, Option<&Term<'_>>)]) -> String {
        self.format_param_sequence(
            &params
                .iter()
                .map(|(name, constraint)| self.param_info(*name, *constraint))
                .collect::<Vec<_>>(),
            ParamStyle::Decl,
        )
    }

    fn format_fun_params(&self, params: &[FunParam<'_>]) -> String {
        self.format_param_sequence(params, ParamStyle::Fun)
    }

    fn format_param_sequence(&self, params: &[FunParam<'_>], style: ParamStyle) -> String {
        if params.is_empty() {
            return String::new();
        }
        let mut rendered = Vec::new();
        let mut i = 0;
        while i < params.len() {
            let current = params[i];
            let current_constraint = current
                .constraint
                .map(|term| self.format_term(term, PREC_BLOCK));
            let mut names = vec![current.name];
            let mut j = i + 1;
            while j < params.len() {
                let next = params[j];
                let next_constraint = next
                    .constraint
                    .map(|term| self.format_term(term, PREC_BLOCK));
                if current.implicit != next.implicit || current_constraint != next_constraint {
                    break;
                }
                names.push(next.name);
                j += 1;
            }
            let piece = match style {
                ParamStyle::Decl => self.format_decl_param_group(
                    &names,
                    current_constraint.as_deref(),
                    current.implicit,
                ),
                ParamStyle::Fun => self.format_fun_param_group(
                    &names,
                    current_constraint.as_deref(),
                    current.implicit,
                ),
            };
            rendered.push(piece);
            i = j;
        }
        rendered.join(" ")
    }

    fn format_decl_param_group(
        &self,
        names: &[&str],
        constraint: Option<&str>,
        implicit: bool,
    ) -> String {
        let open = if implicit { '{' } else { '(' };
        let close = if implicit { '}' } else { ')' };
        match constraint {
            Some(constraint) => {
                format!("{open}{} : {constraint}{close}", names.join(" "))
            }
            None => format!("{open}{}{close}", names.join(" ")),
        }
    }

    fn format_fun_param_group(
        &self,
        names: &[&str],
        constraint: Option<&str>,
        implicit: bool,
    ) -> String {
        match (implicit, constraint) {
            (false, None) => names.join(" "),
            (false, Some("data")) => names.join(" "),
            (true, None) => format!("{{{}}}", names.join(" ")),
            (true, Some("data")) => format!("{{{}}}", names.join(" ")),
            (_, Some(constraint)) => {
                let open = if implicit { '{' } else { '(' };
                let close = if implicit { '}' } else { ')' };
                format!("{open}{} : {constraint}{close}", names.join(" "))
            }
        }
    }

    fn param_info<'bump>(
        &self,
        name: Name<'bump>,
        constraint: Option<&'bump Term<'bump>>,
    ) -> FunParam<'bump> {
        match constraint {
            Some(Term::Implicit(inner)) if is_builtin_data(inner) => FunParam {
                name,
                constraint: None,
                implicit: true,
            },
            Some(Term::Implicit(inner)) => FunParam {
                name,
                constraint: Some(inner),
                implicit: true,
            },
            Some(term) => FunParam {
                name,
                constraint: if is_builtin_data(term) {
                    None
                } else {
                    Some(term)
                },
                implicit: false,
            },
            None => FunParam {
                name,
                constraint: None,
                implicit: false,
            },
        }
    }

    fn format_term(&self, term: &Term<'_>, parent_prec: u8) -> String {
        if let Some((params, body)) = self.decompose_fun(term) {
            let params = self.format_fun_params(&params);
            let body = self.format_term(body, PREC_BLOCK);
            let text = if is_multiline(&body) {
                format!("fun {params} =>\n{}", indent_block(&body, INDENT))
            } else {
                format!("fun {params} => {body}")
            };
            return wrap_prec(text, PREC_BLOCK, parent_prec);
        }

        match term {
            Term::Var(i) => wrap_prec(format!("${i}"), PREC_ATOM, parent_prec),
            Term::LitInt(n) => wrap_prec(n.to_string(), PREC_ATOM, parent_prec),
            Term::LitBool(b) => wrap_prec(b.to_string(), PREC_ATOM, parent_prec),
            Term::LitStr(s) => wrap_prec(format!("\"{}\"", escape_str(s)), PREC_ATOM, parent_prec),
            Term::Universe(u) => wrap_prec(u.to_string(), PREC_ATOM, parent_prec),
            Term::Builtin(name) | Term::Named(name) | Term::Global(name) => {
                wrap_prec((*name).to_string(), PREC_ATOM, parent_prec)
            }
            Term::PrimOp(op) => wrap_prec(op.to_string(), PREC_ATOM, parent_prec),
            Term::Implicit(inner) => self.format_term(inner, parent_prec),
            Term::Lam(body) => {
                let body = self.format_term(body, PREC_BLOCK);
                let text = if is_multiline(&body) {
                    format!("fun _ =>\n{}", indent_block(&body, INDENT))
                } else {
                    format!("fun _ => {body}")
                };
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::NamedLam(_, _) => {
                let (params, body) = self.collect_named_lambdas(term);
                let params = params
                    .into_iter()
                    .map(|name| name.unwrap_or("_"))
                    .collect::<Vec<_>>()
                    .join(" ");
                let body = self.format_term(body, PREC_BLOCK);
                let text = if is_multiline(&body) {
                    format!("fun {params} =>\n{}", indent_block(&body, INDENT))
                } else {
                    format!("fun {params} => {body}")
                };
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::Pi(_, _, _) => {
                let text = self.format_pi(term);
                wrap_prec(text, PREC_ARROW, parent_prec)
            }
            Term::Let(name, value, body, constraint) => {
                let text = self.format_let(name, value, body, *constraint);
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::IfThenElse(cond, then_branch, else_branch) => {
                let text = self.format_if(cond, then_branch, else_branch);
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::Refine(name, parent, predicate) => {
                let parent = self.format_term(parent, PREC_ANNOT);
                let predicate = self.format_term(predicate, PREC_BLOCK);
                let text = if is_multiline(&predicate) {
                    format!(
                        "{parent} where ({name} =>\n{})",
                        indent_block(&predicate, INDENT)
                    )
                } else {
                    format!("{parent} where ({name} => {predicate})")
                };
                wrap_prec(text, PREC_ANNOT, parent_prec)
            }
            Term::Annot(inner, constraint) => {
                let inner = self.format_term(inner, PREC_ANNOT);
                let constraint = self.format_term(constraint, PREC_ANNOT);
                let text = if is_multiline(&inner) || is_multiline(&constraint) {
                    format!("(\n{}\n  : {}\n)", indent_block(&inner, INDENT), constraint)
                } else {
                    format!("({inner} : {constraint})")
                };
                wrap_prec(text, PREC_ANNOT, parent_prec)
            }
            Term::ByProof(inner, tactics) => {
                let text = self.format_by_proof(*inner, tactics);
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::AutoProof => wrap_prec("auto".to_string(), PREC_ATOM, parent_prec),
            Term::RefParam => wrap_prec("x".to_string(), PREC_ATOM, parent_prec),
            Term::EnumDef(_, variants) => {
                let text = self.format_enum(variants);
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::Variant(name, _, payloads) => {
                let mut parts = vec![format!("{name}.mk")];
                parts.extend(
                    payloads
                        .iter()
                        .map(|term| self.format_term(term, PREC_APP + 1)),
                );
                wrap_prec(parts.join(" "), PREC_APP, parent_prec)
            }
            Term::Match(scrutinee, branches) => {
                let text = self.format_resolved_match(scrutinee, branches);
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::NamedMatch(scrutinee, branches) => {
                let text = self.format_named_match(scrutinee, branches);
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::Do(stmts) => wrap_prec(self.format_do(stmts), PREC_BLOCK, parent_prec),
            Term::Unsafe(inner) => {
                let inner = self.format_term(inner, PREC_BLOCK);
                let text = if is_multiline(&inner) {
                    format!("unsafe {{\n{}\n}}", indent_block(&inner, INDENT))
                } else {
                    format!("unsafe {{ {inner} }}")
                };
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::Pure(inner) => {
                let inner = self.format_term(inner, PREC_APP);
                wrap_prec(format!("pure {inner}"), PREC_BLOCK, parent_prec)
            }
            Term::StructDef(_, fields) => {
                let text = self.format_struct(fields);
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::StructCons(name, values) => {
                let mut parts = vec![format!("{name}.mk")];
                parts.extend(
                    values
                        .iter()
                        .map(|term| self.format_term(term, PREC_APP + 1)),
                );
                wrap_prec(parts.join(" "), PREC_APP, parent_prec)
            }
            Term::NamedStructCons(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field, value)| {
                        format!("{field} := {}", self.format_term(value, PREC_BLOCK))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let text = match name {
                    Some(name) => format!("{name}{{{fields}}}"),
                    None => format!("{{{fields}}}"),
                };
                wrap_prec(text, PREC_APP, parent_prec)
            }
            Term::StructProj(subject, idx) => wrap_prec(
                format!("{}.{}", self.format_term(subject, PREC_APP), idx),
                PREC_APP,
                parent_prec,
            ),
            Term::MethodCall(receiver, method) => wrap_prec(
                format!("{}.{}", self.format_term(receiver, PREC_APP), method),
                PREC_APP,
                parent_prec,
            ),
            Term::Quote(inner) => {
                let inner = self.format_term(inner, PREC_BLOCK);
                let text = if is_multiline(&inner) {
                    format!("quote {{\n{}\n}}", indent_block(&inner, INDENT))
                } else {
                    format!("quote {{ {inner} }}")
                };
                wrap_prec(text, PREC_BLOCK, parent_prec)
            }
            Term::Splice(inner) => wrap_prec(
                format!("$({})", self.format_term(inner, PREC_BLOCK)),
                PREC_ATOM,
                parent_prec,
            ),
            Term::App(_, _) => self.format_app(term, parent_prec),
        }
    }

    fn decompose_fun<'bump>(
        &self,
        term: &'bump Term<'bump>,
    ) -> Option<(Vec<FunParam<'bump>>, &'bump Term<'bump>)> {
        let Term::Annot(inner, constraint) = term else {
            return None;
        };
        let (lambda_params, body) = self.collect_named_lambdas(inner);
        if lambda_params.iter().any(|name| name.is_none()) {
            return None;
        }
        let mut cursor = *constraint;
        let mut params = Vec::new();
        for expected_name in lambda_params {
            let Term::Pi(name, domain, rest) = cursor else {
                return None;
            };
            let expected_name = expected_name?;
            if *name != expected_name {
                return None;
            }
            params.push(self.param_info(*name, Some(*domain)));
            cursor = rest;
        }
        if !is_builtin_data(cursor) {
            return None;
        }
        Some((params, body))
    }

    fn collect_named_lambdas<'bump>(
        &self,
        mut term: &'bump Term<'bump>,
    ) -> (Vec<Option<Name<'bump>>>, &'bump Term<'bump>) {
        let mut params = Vec::new();
        loop {
            match term {
                Term::NamedLam(name, body) => {
                    params.push(Some(*name));
                    term = body;
                }
                Term::Lam(body) => {
                    params.push(None);
                    term = body;
                }
                _ => return (params, term),
            }
        }
    }

    fn format_pi(&self, term: &Term<'_>) -> String {
        let mut cursor = term;
        let mut parts = Vec::new();
        while let Term::Pi(name, domain, rest) = cursor {
            let param = self.param_info(*name, Some(*domain));
            let rendered = if param.name.is_empty() && !param.implicit {
                self.format_term(domain, PREC_ARROW + 1)
            } else {
                self.format_decl_param_group(
                    &[param.name],
                    param
                        .constraint
                        .map(|constraint| self.format_term(constraint, PREC_BLOCK))
                        .as_deref(),
                    param.implicit,
                )
            };
            parts.push(rendered);
            cursor = rest;
        }
        parts.push(self.format_term(cursor, PREC_ARROW));
        parts.join(" -> ")
    }

    fn format_let(
        &self,
        name: &str,
        value: &Term<'_>,
        body: &Term<'_>,
        constraint: Option<&Term<'_>>,
    ) -> String {
        let mut head = format!("let {name}");
        if let Some(constraint) = constraint {
            head.push_str(" : ");
            head.push_str(&self.format_term(constraint, PREC_BLOCK));
        }
        let value = self.format_term(value, PREC_BLOCK);
        let body = self.format_term(body, PREC_BLOCK);
        if !is_multiline(&value) && !is_multiline(&body) {
            return format!("{head} := {value} in {body}");
        }
        let value_block = indent_block(&value, INDENT);
        let body_block = indent_block(&body, INDENT);
        format!("{head} :=\n{value_block}\nin\n{body_block}")
    }

    fn format_if(&self, cond: &Term<'_>, then_branch: &Term<'_>, else_branch: &Term<'_>) -> String {
        let cond = self.format_term(cond, PREC_BLOCK);
        let then_branch = self.format_term(then_branch, PREC_BLOCK);
        let else_branch = self.format_term(else_branch, PREC_BLOCK);
        if !is_multiline(&cond) && !is_multiline(&then_branch) && !is_multiline(&else_branch) {
            return format!("if {cond} then {then_branch} else {else_branch}");
        }
        let head = if is_multiline(&cond) {
            format!("if\n{}", indent_block(&cond, INDENT))
        } else {
            format!("if {cond}")
        };
        format!(
            "{head} then\n{}\nelse\n{}",
            indent_block(&then_branch, INDENT),
            indent_block(&else_branch, INDENT)
        )
    }

    fn format_by_proof(&self, inner: Option<&Term<'_>>, tactics: &[Tactic<'_>]) -> String {
        let formatted_tactics = tactics
            .iter()
            .map(|tactic| self.format_tactic(tactic))
            .collect::<Vec<_>>();
        let multiline =
            formatted_tactics.len() > 1 || formatted_tactics.iter().any(|t| is_multiline(t));
        match inner {
            Some(inner) => {
                let inner = self.format_term(inner, PREC_BLOCK);
                if !multiline && !is_multiline(&inner) {
                    return format!("{inner} by {}", formatted_tactics[0]);
                }
                format!(
                    "{} by\n{}",
                    maybe_wrap_multiline(inner),
                    indent_block(
                        &formatted_tactics
                            .iter()
                            .enumerate()
                            .map(|(idx, tactic)| {
                                if idx + 1 == formatted_tactics.len() {
                                    tactic.clone()
                                } else {
                                    format!("{tactic};")
                                }
                            })
                            .collect::<Vec<_>>()
                            .join("\n"),
                        INDENT,
                    )
                )
            }
            None => {
                if !multiline {
                    return format!("by {}", formatted_tactics[0]);
                }
                format!(
                    "by\n{}",
                    indent_block(
                        &formatted_tactics
                            .iter()
                            .enumerate()
                            .map(|(idx, tactic)| {
                                if idx + 1 == formatted_tactics.len() {
                                    tactic.clone()
                                } else {
                                    format!("{tactic};")
                                }
                            })
                            .collect::<Vec<_>>()
                            .join("\n"),
                        INDENT,
                    )
                )
            }
        }
    }

    fn format_tactic(&self, tactic: &Tactic<'_>) -> String {
        match tactic {
            Tactic::Exact(term) => format!(
                "exact {}",
                maybe_wrap_multiline(self.format_term(term, PREC_BLOCK))
            ),
            Tactic::Apply(term) => format!(
                "apply {}",
                maybe_wrap_multiline(self.format_term(term, PREC_BLOCK))
            ),
            Tactic::Intro(Some(name)) => format!("intro {name}"),
            Tactic::Intro(None) => "intro".to_string(),
            Tactic::Have(name, term) => {
                format!(
                    "have {name} := {}",
                    maybe_wrap_multiline(self.format_term(term, PREC_BLOCK))
                )
            }
            Tactic::Custom(name, args) => {
                let args = args
                    .iter()
                    .map(|arg| maybe_wrap_multiline(self.format_term(arg, PREC_BLOCK)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name}({args})")
            }
        }
    }

    fn format_enum(&self, variants: &[(Name<'_>, &[(Name<'_>, &Term<'_>)])]) -> String {
        let mut lines = vec!["enum".to_string()];
        for (name, fields) in variants {
            if fields.is_empty() {
                lines.push(format!("| {name}"));
                continue;
            }
            let fields = fields
                .iter()
                .map(|(field, ty)| format!("({field} : {})", self.format_term(ty, PREC_BLOCK)))
                .collect::<Vec<_>>()
                .join(" ");
            lines.push(format!("| {name} of {fields}"));
        }
        lines
            .into_iter()
            .enumerate()
            .map(|(idx, line)| {
                if idx == 0 {
                    line
                } else {
                    format!("{}{}", " ".repeat(INDENT), line)
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn format_struct(&self, fields: &[(Name<'_>, &Term<'_>)]) -> String {
        let mut lines = vec!["struct".to_string()];
        lines.extend(fields.iter().map(|(name, ty)| {
            format!(
                "{}{} : {}",
                " ".repeat(INDENT),
                name,
                self.format_term(ty, PREC_BLOCK)
            )
        }));
        lines.join("\n")
    }

    fn format_named_match(
        &self,
        scrutinee: &Term<'_>,
        branches: &[(Name<'_>, &[(Name<'_>, &Term<'_>)], &Term<'_>)],
    ) -> String {
        let mut lines = vec![format!(
            "match {} with",
            self.format_term(scrutinee, PREC_BLOCK)
        )];
        for (variant, binds, body) in branches {
            let mut branch = format!("| {variant}");
            if !binds.is_empty() {
                branch.push(' ');
                branch.push_str(
                    &binds
                        .iter()
                        .map(|(name, _)| (*name).to_string())
                        .collect::<Vec<_>>()
                        .join(" "),
                );
            }
            let body = self.format_term(body, PREC_BLOCK);
            if is_multiline(&body) {
                lines.push(format!(
                    "{}{} =>\n{}",
                    " ".repeat(INDENT),
                    branch,
                    indent_block(&body, INDENT * 2)
                ));
            } else {
                lines.push(format!("{}{} => {}", " ".repeat(INDENT), branch, body));
            }
        }
        lines.join("\n")
    }

    fn format_resolved_match(
        &self,
        scrutinee: &Term<'_>,
        branches: &[(usize, &[(Name<'_>, &Term<'_>)], &Term<'_>)],
    ) -> String {
        let mut lines = vec![format!(
            "match {} with",
            self.format_term(scrutinee, PREC_BLOCK)
        )];
        for (idx, binds, body) in branches {
            let mut branch = format!("| _v{idx}");
            if !binds.is_empty() {
                branch.push(' ');
                branch.push_str(
                    &binds
                        .iter()
                        .map(|(name, _)| (*name).to_string())
                        .collect::<Vec<_>>()
                        .join(" "),
                );
            }
            let body = self.format_term(body, PREC_BLOCK);
            if is_multiline(&body) {
                lines.push(format!(
                    "{}{} =>\n{}",
                    " ".repeat(INDENT),
                    branch,
                    indent_block(&body, INDENT * 2)
                ));
            } else {
                lines.push(format!("{}{} => {}", " ".repeat(INDENT), branch, body));
            }
        }
        lines.join("\n")
    }

    fn format_do(&self, stmts: &[DoStmt<'_>]) -> String {
        let mut lines = vec!["do".to_string()];
        for stmt in stmts {
            let rendered = match stmt {
                DoStmt::Bind(name, rhs) => {
                    let rhs = self.format_term(rhs, PREC_BLOCK);
                    if is_multiline(&rhs) {
                        format!("{name} <-\n{}", indent_block(&rhs, INDENT))
                    } else {
                        format!("{name} <- {rhs}")
                    }
                }
                DoStmt::Let(name, rhs, constraint) => {
                    let mut head = format!("let {name}");
                    if let Some(constraint) = constraint {
                        head.push_str(" : ");
                        head.push_str(&self.format_term(constraint, PREC_BLOCK));
                    }
                    let rhs = self.format_term(rhs, PREC_BLOCK);
                    if is_multiline(&rhs) {
                        format!("{head} :=\n{}", indent_block(&rhs, INDENT))
                    } else {
                        format!("{head} := {rhs}")
                    }
                }
                DoStmt::Expr(expr) => self.format_term(expr, PREC_BLOCK),
            };
            lines.push(indent_block(&rendered, INDENT));
        }
        lines.join("\n")
    }

    fn format_app(&self, term: &Term<'_>, parent_prec: u8) -> String {
        if let Some(inner) = unary_neg_arg(term) {
            let inner = self.format_term(inner, PREC_APP);
            return wrap_prec(format!("-{inner}"), PREC_APP, parent_prec);
        }

        if let Some((op, lhs, rhs)) = infix_app(term) {
            let prec = infix_prec(op);
            let lhs = self.format_term(lhs, prec);
            let rhs = self.format_term(rhs, prec + 1);
            return wrap_prec(format!("{lhs} {op} {rhs}"), prec, parent_prec);
        }

        let (head, args) = collect_app_spine(term);
        let mut parts = vec![self.format_term(head, PREC_APP)];
        parts.extend(args.into_iter().map(|arg| {
            let rendered = self.format_term(arg, PREC_ATOM);
            if is_multiline(&rendered) {
                wrap_parens(rendered)
            } else {
                rendered
            }
        }));
        wrap_prec(parts.join(" "), PREC_APP, parent_prec)
    }
}

#[derive(Clone, Copy)]
enum ParamStyle {
    Decl,
    Fun,
}

fn infix_prec(op: PrimOp) -> u8 {
    match op {
        PrimOp::Eq | PrimOp::Lt | PrimOp::Gt | PrimOp::Le | PrimOp::Ge | PrimOp::Neq => {
            PREC_COMPARE
        }
        PrimOp::Add | PrimOp::Sub => PREC_ADD,
        PrimOp::Mul | PrimOp::Div | PrimOp::Mod_ => PREC_MUL,
    }
}

fn collect_app_spine<'a>(mut term: &'a Term<'a>) -> (&'a Term<'a>, Vec<&'a Term<'a>>) {
    let mut args = Vec::new();
    while let Term::App(fun, arg) = term {
        args.push(*arg);
        term = fun;
    }
    args.reverse();
    (term, args)
}

fn infix_app<'a>(term: &'a Term<'a>) -> Option<(PrimOp, &'a Term<'a>, &'a Term<'a>)> {
    let Term::App(fun, rhs) = term else {
        return None;
    };
    let Term::App(op, lhs) = *fun else {
        return None;
    };
    let Term::PrimOp(op) = *op else {
        return None;
    };
    Some((*op, lhs, rhs))
}

fn unary_neg_arg<'a>(term: &'a Term<'a>) -> Option<&'a Term<'a>> {
    let (op, lhs, rhs) = infix_app(term)?;
    if op == PrimOp::Sub && matches!(lhs, Term::LitInt(0)) {
        Some(rhs)
    } else {
        None
    }
}

fn wrap_prec(text: String, own_prec: u8, parent_prec: u8) -> String {
    if own_prec < parent_prec {
        wrap_parens(text)
    } else {
        text
    }
}

fn wrap_parens(text: String) -> String {
    if is_multiline(&text) {
        format!("(\n{}\n)", indent_block(&text, INDENT))
    } else {
        format!("({text})")
    }
}

fn maybe_wrap_multiline(text: String) -> String {
    if is_multiline(&text) {
        wrap_parens(text)
    } else {
        text
    }
}

fn indent_block(text: &str, spaces: usize) -> String {
    let pad = " ".repeat(spaces);
    text.lines()
        .map(|line| {
            if line.is_empty() {
                String::new()
            } else {
                format!("{pad}{line}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn is_multiline(text: &str) -> bool {
    text.contains('\n')
}

fn is_builtin_data(term: &Term<'_>) -> bool {
    matches!(term, Term::Builtin("data"))
}

fn escape_str(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            other => out.push(other),
        }
    }
    out
}

fn collect_format_targets(path: &Path) -> Result<Vec<PathBuf>, std::io::Error> {
    fn visit(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), std::io::Error> {
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                let skip = path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| matches!(name, ".git" | "target"));
                if !skip {
                    visit(&path, out)?;
                }
                continue;
            }
            if path.extension().and_then(|ext| ext.to_str()) == Some("lig") {
                out.push(path);
            }
        }
        Ok(())
    }

    let mut files = Vec::new();
    if path.is_file() {
        files.push(path.to_path_buf());
    } else {
        visit(path, &mut files)?;
    }
    files.sort();
    Ok(files)
}

#[cfg(test)]
mod tests {
    use super::format_source;
    use bumpalo::Bump;
    use ligare::core::pool::TermArena;
    use ligare::front::parser::parse_program;

    fn assert_roundtrip(source: &str, expected: &str) {
        let formatted = format_source(source).unwrap();
        assert_eq!(formatted, expected);
        let reformatted = format_source(&formatted).unwrap();
        assert_eq!(reformatted, expected);

        let bump = Bump::new();
        let arena = TermArena::new(&bump);
        parse_program(&formatted, &bump, &arena).unwrap();
    }

    #[test]
    fn formats_tops_and_do_blocks() {
        assert_roundtrip(
            "use std::data::nat::Nat, std::primitive::*\npub def main:IO ():=
do\nlet x:int=5\nlet y:=x+1\ny\n",
            "use std::data::nat::Nat, std::primitive::*\n\npub def main : IO () :=\n  do\n    let x : int := 5\n    let y := x + 1\n    y\n",
        );
    }

    #[test]
    fn formats_match_and_namespace() {
        assert_roundtrip(
            "namespace Ops{pub def run (n:int):int:=match n with|Zero=>0|Succ m=>m}\n",
            "namespace Ops {\n  pub def run (n : int) : int :=\n    match n with\n      | Zero => 0\n      | Succ m => m\n}\n",
        );
    }

    #[test]
    fn formats_fun_and_struct_enum_bodies() {
        assert_roundtrip(
            "def wrap:prop:=struct\nx:int\n\
             \n\
             def mk:(int->int):=fun (x:int)=>x\n\
             def option (A:prop):prop:=enum\n|Some of (value:A)\n|None\n",
            "def wrap : prop :=\n  struct\n    x : int\n\n\
             def mk : int -> int := fun (x : int) => x\n\n\
             def option (A : prop) : prop :=\n  enum\n    | Some of (value : A)\n    | None\n",
        );
    }
}
