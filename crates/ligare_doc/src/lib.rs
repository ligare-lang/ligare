use std::path::{Path, PathBuf};

use bumpalo::Bump;
use ligare::core::pool::TermArena;
use ligare::core::syntax::{Name, Term};
use ligare::front::parser::{Attribute, TopLevel, parse_program};
use ligare::pretty::PrettyPrinter;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DocOptions {
    pub include_private: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DocItem {
    full_name: String,
    kind: &'static str,
    signature: Option<String>,
    attributes: Vec<String>,
    doc: Option<String>,
    details: Option<DocDetails>,
    children: Vec<DocItem>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DocDetails {
    Fields(Vec<String>),
    Variants(Vec<String>),
}

struct TopMeta<'a, 'bump> {
    attrs: Vec<&'a Attribute<'bump>>,
    public: bool,
    inner: &'a TopLevel<'bump>,
}

pub fn generate_markdown(path: &Path, options: &DocOptions) -> Result<String, String> {
    let files = collect_doc_targets(path)
        .map_err(|err| format!("cannot read `{}`: {err}", path.display()))?;
    if files.is_empty() {
        return Err(format!("no .lig files found under `{}`", path.display()));
    }

    let base = if path.is_dir() {
        path
    } else {
        path.parent().unwrap_or_else(|| Path::new("."))
    };

    let mut rendered_files = Vec::new();
    for file in files {
        let source = std::fs::read_to_string(&file)
            .map_err(|err| format!("cannot read `{}`: {err}", file.display()))?;
        let bump = Bump::new();
        let arena = TermArena::new(&bump);
        let tops = parse_program(&source, &bump, &arena)
            .map_err(|err| format!("{}: {}", file.display(), err))?;
        let label = path_label(&file, base);
        let body = render_file(&label, &source, &tops, options);
        if !body.is_empty() {
            rendered_files.push((label, body));
        }
    }

    if rendered_files.is_empty() {
        return Ok("# Ligare Documentation\n".to_string());
    }

    if rendered_files.len() == 1 {
        let (label, body) = rendered_files.remove(0);
        return Ok(format!("# `{label}`\n\n{body}\n"));
    }

    let mut out = String::from("# Ligare Documentation\n");
    for (label, body) in rendered_files {
        out.push_str("\n## `");
        out.push_str(&label);
        out.push_str("`\n\n");
        out.push_str(&body);
        out.push('\n');
    }
    Ok(out)
}

pub fn doc_comment_before(source: &str, start: usize) -> Option<String> {
    if let Some(doc) = block_doc_comment_before(source, start) {
        return Some(doc);
    }

    let start = skip_horizontal_space_back(source, start);
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

fn render_file(_label: &str, source: &str, tops: &[TopLevel<'_>], options: &DocOptions) -> String {
    let items = tops
        .iter()
        .filter_map(|top| collect_item(top, source, options, &[], true))
        .collect::<Vec<_>>();
    items
        .iter()
        .map(|item| render_item(item, 2))
        .collect::<Vec<_>>()
        .join("\n\n")
}

fn collect_item(
    top: &TopLevel<'_>,
    source: &str,
    options: &DocOptions,
    prefix: &[String],
    parent_public: bool,
) -> Option<DocItem> {
    let meta = top_meta(top);
    let in_public_scope = parent_public && meta.public;
    let visible = options.include_private || in_public_scope;
    let start = top_start(top);

    match meta.inner {
        TopLevel::TLDef(name, params, ret, body, _) => visible.then(|| DocItem {
            full_name: join_name(prefix, name),
            kind: "Definition",
            signature: Some(render_def_signature(
                &join_name(prefix, name),
                params,
                *ret,
                body,
                meta.public,
            )),
            attributes: render_attributes(&meta.attrs),
            doc: doc_comment_before(source, start),
            details: body_details(body),
            children: Vec::new(),
        }),
        TopLevel::TLExternDef(name, params, ret, _) => visible.then(|| DocItem {
            full_name: join_name(prefix, name),
            kind: "External Definition",
            signature: Some(render_extern_signature(
                &join_name(prefix, name),
                params,
                ret,
                meta.public,
            )),
            attributes: render_attributes(&meta.attrs),
            doc: doc_comment_before(source, start),
            details: None,
            children: Vec::new(),
        }),
        TopLevel::TLInstance(name, constraint, _, _) => visible.then(|| DocItem {
            full_name: join_name(prefix, name),
            kind: "Instance",
            signature: Some(render_instance_signature(
                &join_name(prefix, name),
                constraint,
            )),
            attributes: render_attributes(&meta.attrs),
            doc: doc_comment_before(source, start),
            details: None,
            children: Vec::new(),
        }),
        TopLevel::TLTheorem(name, prop, _, _) => visible.then(|| DocItem {
            full_name: join_name(prefix, name),
            kind: "Theorem",
            signature: Some(render_theorem_signature(
                &join_name(prefix, name),
                prop,
                meta.public,
            )),
            attributes: render_attributes(&meta.attrs),
            doc: doc_comment_before(source, start),
            details: None,
            children: Vec::new(),
        }),
        TopLevel::TLMod(name, _) => visible.then(|| DocItem {
            full_name: join_name(prefix, name),
            kind: "Module",
            signature: Some(format!(
                "{}mod {}",
                visibility_prefix(meta.public),
                join_name(prefix, name)
            )),
            attributes: render_attributes(&meta.attrs),
            doc: doc_comment_before(source, start),
            details: None,
            children: Vec::new(),
        }),
        TopLevel::TLNamespace(name, items, _) => {
            let mut child_prefix = prefix.to_vec();
            child_prefix.push((*name).to_string());
            let children = items
                .iter()
                .filter_map(|item| {
                    collect_item(item, source, options, &child_prefix, in_public_scope)
                })
                .collect::<Vec<_>>();
            if !visible && children.is_empty() {
                return None;
            }
            Some(DocItem {
                full_name: join_name(prefix, name),
                kind: "Namespace",
                signature: Some(format!(
                    "{}namespace {}",
                    visibility_prefix(meta.public),
                    join_name(prefix, name)
                )),
                attributes: render_attributes(&meta.attrs),
                doc: doc_comment_before(source, start),
                details: None,
                children,
            })
        }
        TopLevel::TLVariable(_, _)
        | TopLevel::TLUse(_, _, _)
        | TopLevel::TLCheck(_, _, _)
        | TopLevel::TLEval(_, _)
        | TopLevel::TLExpr(_, _)
        | TopLevel::TLSplice(_, _) => None,
        TopLevel::TLPublic(_) | TopLevel::TLAttributed(..) => unreachable!(),
    }
}

fn render_item(item: &DocItem, level: usize) -> String {
    let mut out = format!(
        "{} `{}`\n\n_{}_",
        "#".repeat(level),
        item.full_name,
        item.kind
    );
    if let Some(signature) = &item.signature {
        out.push_str("\n\n```ligare\n");
        out.push_str(signature);
        out.push_str("\n```");
    }
    if !item.attributes.is_empty() {
        out.push_str("\n\nAttributes: ");
        out.push_str(&item.attributes.join(", "));
    }
    if let Some(doc) = &item.doc
        && !doc.trim().is_empty()
    {
        out.push_str("\n\n");
        out.push_str(doc.trim());
    }
    if let Some(details) = &item.details {
        match details {
            DocDetails::Fields(fields) if !fields.is_empty() => {
                out.push_str("\n\nFields:\n");
                for field in fields {
                    out.push_str("- `");
                    out.push_str(field);
                    out.push_str("`\n");
                }
                out.pop();
            }
            DocDetails::Variants(variants) if !variants.is_empty() => {
                out.push_str("\n\nVariants:\n");
                for variant in variants {
                    out.push_str("- `");
                    out.push_str(variant);
                    out.push_str("`\n");
                }
                out.pop();
            }
            _ => {}
        }
    }
    if !item.children.is_empty() {
        let children = item
            .children
            .iter()
            .map(|child| render_item(child, level + 1))
            .collect::<Vec<_>>()
            .join("\n\n");
        out.push_str("\n\n");
        out.push_str(&children);
    }
    out
}

fn render_def_signature(
    full_name: &str,
    params: &[(Name<'_>, Option<&Term<'_>>)],
    ret: Option<&Term<'_>>,
    body: &Term<'_>,
    public: bool,
) -> String {
    let mut out = format!("{}def {}", visibility_prefix(public), full_name);
    let params = render_params(params);
    if !params.is_empty() {
        out.push(' ');
        out.push_str(&params);
    }
    if let Some(ret) = ret.or_else(|| inferred_zero_arity_constraint(params.is_empty(), body)) {
        out.push_str(" : ");
        out.push_str(&render_term(ret));
    }
    out
}

fn render_extern_signature(
    full_name: &str,
    params: &[(Name<'_>, Option<&Term<'_>>)],
    ret: &Term<'_>,
    public: bool,
) -> String {
    let mut out = format!("{}extern def {}", visibility_prefix(public), full_name);
    let params = render_params(params);
    if !params.is_empty() {
        out.push(' ');
        out.push_str(&params);
    }
    out.push_str(" : ");
    out.push_str(&render_term(ret));
    out
}

fn render_instance_signature(full_name: &str, constraint: &Term<'_>) -> String {
    format!("instance {full_name} : {}", render_term(constraint))
}

fn render_theorem_signature(full_name: &str, prop: &Term<'_>, public: bool) -> String {
    format!(
        "{}theorem {} : {}",
        visibility_prefix(public),
        full_name,
        render_term(prop)
    )
}

fn render_params(params: &[(Name<'_>, Option<&Term<'_>>)]) -> String {
    params
        .iter()
        .map(|(name, constraint)| render_param(name, *constraint))
        .collect::<Vec<_>>()
        .join(" ")
}

fn render_param(name: &str, constraint: Option<&Term<'_>>) -> String {
    match constraint {
        Some(Term::Implicit(inner)) if is_builtin_data(inner) => format!("{{{name}}}"),
        Some(Term::Implicit(inner)) => format!("{{{name} : {}}}", render_term(inner)),
        Some(inner) if is_builtin_data(inner) => format!("({name})"),
        Some(inner) => format!("({name} : {})", render_term(inner)),
        None => format!("({name})"),
    }
}

fn render_attributes(attrs: &[&Attribute<'_>]) -> Vec<String> {
    attrs.iter().map(|attr| render_attribute(attr)).collect()
}

fn render_attribute(attr: &Attribute<'_>) -> String {
    let path = attr.path.join("::");
    if attr.args.is_empty() {
        return format!("`#[{path}]`");
    }
    let args = attr
        .args
        .iter()
        .map(|arg| render_term(arg))
        .collect::<Vec<_>>()
        .join(", ");
    format!("`#[{path}({args})]`")
}

fn body_details(body: &Term<'_>) -> Option<DocDetails> {
    let inner = strip_annot(body);
    match inner {
        Term::StructDef(_, fields) => Some(DocDetails::Fields(
            fields
                .iter()
                .map(|(name, constraint)| format!("{name} : {}", render_term(constraint)))
                .collect(),
        )),
        Term::EnumDef(_, variants) => Some(DocDetails::Variants(
            variants
                .iter()
                .map(|(name, fields)| {
                    if fields.is_empty() {
                        (*name).to_string()
                    } else {
                        format!(
                            "{} of {}",
                            name,
                            fields
                                .iter()
                                .map(|(field, constraint)| {
                                    format!("({field} : {})", render_term(constraint))
                                })
                                .collect::<Vec<_>>()
                                .join(" ")
                        )
                    }
                })
                .collect(),
        )),
        _ => None,
    }
}

fn strip_annot<'a>(mut term: &'a Term<'a>) -> &'a Term<'a> {
    while let Term::Annot(inner, _) = term {
        term = inner;
    }
    term
}

fn inferred_zero_arity_constraint<'a>(
    has_no_params: bool,
    body: &'a Term<'a>,
) -> Option<&'a Term<'a>> {
    if !has_no_params {
        return None;
    }
    match body {
        Term::Annot(_, constraint) => Some(*constraint),
        _ => None,
    }
}

fn render_term(term: &Term<'_>) -> String {
    PrettyPrinter::pretty(term)
}

fn join_name(prefix: &[String], name: &str) -> String {
    if prefix.is_empty() {
        return name.to_string();
    }
    let mut parts = prefix.to_vec();
    parts.push(name.to_string());
    parts.join("::")
}

fn visibility_prefix(public: bool) -> &'static str {
    if public { "pub " } else { "" }
}

fn is_builtin_data(term: &Term<'_>) -> bool {
    matches!(term, Term::Builtin("data"))
}

fn top_meta<'a, 'bump>(mut top: &'a TopLevel<'bump>) -> TopMeta<'a, 'bump> {
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

fn top_start(top: &TopLevel<'_>) -> usize {
    match top {
        TopLevel::TLDef(_, _, _, _, span)
        | TopLevel::TLExternDef(_, _, _, span)
        | TopLevel::TLInstance(_, _, _, span)
        | TopLevel::TLVariable(_, span)
        | TopLevel::TLTheorem(_, _, _, span)
        | TopLevel::TLUse(_, _, span)
        | TopLevel::TLMod(_, span)
        | TopLevel::TLNamespace(_, _, span)
        | TopLevel::TLCheck(_, _, span)
        | TopLevel::TLEval(_, span)
        | TopLevel::TLExpr(_, span)
        | TopLevel::TLSplice(_, span)
        | TopLevel::TLAttributed(_, _, span) => span.start,
        TopLevel::TLPublic(inner) => top_start(inner),
    }
}

fn collect_doc_targets(path: &Path) -> Result<Vec<PathBuf>, std::io::Error> {
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

fn path_label(path: &Path, base: &Path) -> String {
    path.strip_prefix(base)
        .unwrap_or(path)
        .display()
        .to_string()
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

#[cfg(test)]
mod tests {
    use super::{DocOptions, doc_comment_before, generate_markdown};

    #[test]
    fn line_doc_comment_is_collected() {
        let source = "-- | Adds one\npub def inc (x : int) : int := x + 1\n";
        let start = source.find("pub def").unwrap();
        assert_eq!(
            doc_comment_before(source, start).as_deref(),
            Some("Adds one")
        );
    }

    #[test]
    fn markdown_lists_signatures_and_variants() {
        let root = std::env::temp_dir().join(format!(
            "ligare_doc_test_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(root.join("src")).unwrap();
        std::fs::write(
            root.join("src/lib.lig"),
            "-- | API root\npub namespace Api {\n  -- | Greeting type\n  pub def Greeting : prop := enum\n    | Hello\n    | Named of (value : str)\n}\n",
        )
        .unwrap();

        let markdown = generate_markdown(&root, &DocOptions::default()).unwrap();
        assert!(markdown.contains("`src/lib.lig`"), "{markdown}");
        assert!(markdown.contains("`Api`"), "{markdown}");
        assert!(markdown.contains("`Api::Greeting`"), "{markdown}");
        assert!(markdown.contains("Greeting type"), "{markdown}");
        assert!(markdown.contains("Variants:"), "{markdown}");
        assert!(markdown.contains("`Named of (value : str)`"), "{markdown}");
    }
}
