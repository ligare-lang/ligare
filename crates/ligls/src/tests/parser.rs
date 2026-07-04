use super::*;

#[test]
fn normal_program_reuses_ligare_ast() {
    let (bump, arena) = arena();
    let source = r#"
mod app
pub use std::io
def Point : prop := struct
  x : int
  y : int
def Option : prop := enum
  | None
  | Some of (value : int)
def main : int := match Option.Some 1 with | Some value => value | None => 0
#eval Point.x
"#;

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(ast.top_levels().count(), 6);
    assert!(matches!(
        ast.items[0],
        AstNode::TopLevel(TopLevel::TLMod(..))
    ));
    assert!(matches!(
        ast.items[1],
        AstNode::TopLevel(TopLevel::TLUse(_, Visibility::Public, _))
    ));
    assert!(matches!(
        ast.items[5],
        AstNode::TopLevel(TopLevel::TLEval(term, _)) if matches!(*term, Term::Named("Point.x"))
    ));
}

#[test]
fn global_allocator_attribute_is_parsed_with_following_def() {
    let (bump, arena) = arena();
    let source = "#[global_allocator]\ndef alloc : int := 1\ndef after : int := 2";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(ast.top_levels().count(), 2);
    let alloc_name = format!("{GLOBAL_ALLOCATOR_NAME_PREFIX}alloc");
    assert!(matches!(
        ast.items[0],
        AstNode::TopLevel(TopLevel::TLAttributed(_, inner, _))
            if matches!(*inner, TopLevel::TLDef(name, ..) if name == alloc_name)
    ));
    assert!(
        matches!(ast.items[1], AstNode::TopLevel(TopLevel::TLDef(name, ..)) if name == "after")
    );
}

#[test]
fn shared_constraint_param_group_reuses_ligare_ast() {
    let (bump, arena) = arena();
    let source = "def add (a b : int) : int := a + b";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(ast.top_levels().count(), 1);
    assert!(
        matches!(ast.items[0], AstNode::TopLevel(TopLevel::TLDef(_, params, _, _, _)) if params.len() == 2)
    );
}

#[test]
fn single_error_produces_partial_ast_and_error_node() {
    let (bump, arena) = arena();
    let source = "def good : int := 1\ndef broken : int := if true then\n#eval good";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(!errors.is_empty());
    assert!(matches!(
        ast.items[0],
        AstNode::TopLevel(TopLevel::TLDef(..))
    ));
    assert!(matches!(ast.items[1], AstNode::Error(_)));
    assert!(matches!(
        ast.items[2],
        AstNode::TopLevel(TopLevel::TLEval(..))
    ));
}

#[test]
fn bare_top_level_expression_does_not_emit_header_error() {
    let (bump, arena) = arena();

    let (ast, errors) = parse_program_lsp("1 + 2", bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert!(matches!(
        ast.items[0],
        AstNode::TopLevel(TopLevel::TLExpr(..))
    ));
}

#[test]
fn multiple_errors_are_reported_and_recovered() {
    let (bump, arena) = arena();
    let source = "def := 1\ndef ok : int := 2\n#check : int\ndef tail : int := 3";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.len() >= 2, "{errors:?}");
    assert!(matches!(ast.items[0], AstNode::Error(_)));
    assert!(matches!(
        ast.items[1],
        AstNode::TopLevel(TopLevel::TLDef(..))
    ));
    assert!(matches!(ast.items[2], AstNode::Error(_)));
    assert!(matches!(
        ast.items[3],
        AstNode::TopLevel(TopLevel::TLDef(..))
    ));
}

#[test]
fn nested_error_does_not_hide_following_definition() {
    let (bump, arena) = arena();
    let source = r#"
def bad : int := do {
  let x := 1;
  if true then 1 else
def after : int := 42
"#;

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(!errors.is_empty());
    assert!(matches!(ast.items[0], AstNode::Error(_)));
    assert!(
        matches!(ast.items[1], AstNode::TopLevel(TopLevel::TLDef(name, ..)) if name == "after")
    );
}

#[test]
fn diagnostics_check_eval_like_forms_in_quiet_mode() {
    for source in ["#eval missing", "missing"] {
        let diagnostics = lsp_diagnostics_for_source(source, DiagnosticCheck::Fast);
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("unbound: missing")),
            "{diagnostics:#?}"
        );
    }
}

#[test]
fn metaprogramming_syntax_reuses_ligare_ast() {
    let (bump, arena) = arena();
    let source = "#eval $(quote { 1 + 2 })";

    let (ast, errors) = parse_program_lsp(source, bump, &arena);

    assert!(errors.is_empty(), "{errors:?}");
    assert!(
        matches!(ast.items[0], AstNode::TopLevel(TopLevel::TLEval(term, _)) if matches!(*term, Term::Splice(_)))
    );
}

#[test]
fn diagnostics_expand_quote_and_splice() {
    let ok = lsp_diagnostics_for_source("#check quote { 1 + 2 } : Expr", DiagnosticCheck::Fast);
    assert!(ok.is_empty(), "{ok:#?}");

    let bad = lsp_diagnostics_for_source("def bad : int := $(1)", DiagnosticCheck::Fast);
    assert!(
        bad.iter().any(|diagnostic| diagnostic
            .message
            .contains("splice expression must have type Expr")),
        "{bad:#?}"
    );
}
