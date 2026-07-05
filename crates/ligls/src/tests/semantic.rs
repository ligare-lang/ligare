use super::*;

#[test]
fn semantic_tokens_classify_semantic_identifier_kinds() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
mod math
pub use std::io::print
pub def Option : prop := enum
  | None
  | Some of (value : int)
def Point : prop := struct
  x : int
def add (x : int) (y : int) : int := x + y
def opt : Option := Option::Some 1
#check let p : Point := Point.mk 1 in Point.x p : int
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "def", "keyword");
    assert_token(&decoded, "add", "function");
    assert_token(&decoded, "opt", "variable");
    assert_token(&decoded, "Some", "constructor");
    assert_token(&decoded, "Option", "constraint");
    assert_token(&decoded, "Point", "constraint");
    assert_token(&decoded, "math", "namespace");
    assert_token(&decoded, "std", "namespace");
    assert_token(&decoded, "x", "parameter");
    assert!(
        decoded.iter().any(|token| {
            token.text == "Option"
                && token.kind == "constraint"
                && token.modifiers.contains(&"public")
        }),
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_namespace_members_and_qualified_references() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
namespace Ops {
  pub def inc (x : int) : int := x + 1
  pub def Flag : prop := enum
    | On
}
#eval Ops::inc 1
#check Ops::Flag::On : Ops::Flag
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert!(
        decoded
            .iter()
            .filter(|token| token.text == "Ops" && token.kind == "namespace")
            .count()
            >= 3,
        "{decoded:#?}"
    );
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "inc" && token.kind == "function")
            .count(),
        2,
        "{decoded:#?}"
    );
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "Flag" && token.kind == "constraint")
            .count(),
        3,
        "{decoded:#?}"
    );
    assert_token(&decoded, "On", "constructor");
}

#[test]
fn semantic_tokens_legend_exposes_constraints_as_lsp_types() {
    let legend = crate::semantic_tokens_legend();

    assert_eq!(
        legend.token_types[3],
        lsp::SemanticTokenType::TYPE,
        "semantic constraints are user-facing types and should use the standard LSP token type"
    );
}

#[test]
fn semantic_tokens_legend_exposes_attributes_as_lsp_decorators() {
    let legend = crate::semantic_tokens_legend();

    assert_eq!(
        legend.token_types[8],
        lsp::SemanticTokenType::DECORATOR,
        "language attributes should use the standard LSP decorator token type"
    );
}

#[test]
fn semantic_tokens_classify_attribute_paths() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def target : int := 1
#[meta::rewrite("x", target)]
def value : int := target
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "meta", "attribute");
    assert_token(&decoded, "rewrite", "attribute");
    assert!(
        decoded
            .iter()
            .filter(|token| token.text == "target" && token.kind == "attribute")
            .count()
            == 0,
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_builtin_constraints() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = format!(
        "#check 0 : {}\n",
        BUILTIN_CONSTRAINT_NAMES.join("\n#check 0 : ")
    );

    cache.update_fast(uri.clone(), Some(1), source.clone());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(&source, &tokens);

    for builtin in BUILTIN_CONSTRAINT_NAMES {
        assert_token(&decoded, builtin, "constraint");
    }
}

#[test]
fn semantic_tokens_classify_refinement_constraint_aliases() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def Nat := int where (x => x >= 0)
def zero : Nat := 0
#check zero : Nat
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert!(
        decoded.iter().any(|token| {
            token.text == "Nat"
                && token.kind == "constraint"
                && token.modifiers.contains(&"definition")
        }),
        "{decoded:#?}"
    );
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "Nat" && token.kind == "constraint")
            .count(),
        3,
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_parameterized_constraint_definitions() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def Option (A : prop) : prop := enum
  | None
  | Some of (value : A)
def maybe : Option int := Some 1
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert!(
        decoded.iter().any(|token| {
            token.text == "Option"
                && token.kind == "constraint"
                && token.modifiers.contains(&"definition")
        }),
        "{decoded:#?}"
    );
    assert!(
        decoded
            .iter()
            .any(|token| token.text == "Option" && token.kind == "constraint"),
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_type_parameters_as_constraints() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def id (A : prop) (x : A) : A := x
def Option (A : prop) : prop := enum
  | None
  | Some of (value : A)
def map (A : prop) (opt : Option A) : Option A := opt
def implicit {B : prop} (y : B) : B := y
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "A" && token.kind == "constraint")
            .count(),
        8,
        "{decoded:#?}"
    );
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "B" && token.kind == "constraint")
            .count(),
        3,
        "{decoded:#?}"
    );
    assert_token(&decoded, "x", "parameter");
    assert_token(&decoded, "y", "parameter");
    assert!(
        decoded
            .iter()
            .all(|token| !matches!(token.text.as_str(), "A" | "B") || token.kind != "parameter"),
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_classify_interface_instances() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
def ShowInt : prop := struct
  show : int -> str
def show_int (x : int) : str := "int"
instance showInt : ShowInt := ShowInt.mk show_int
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "instance", "keyword");
    assert_token(&decoded, "showInt", "variable");
    assert_token(&decoded, "ShowInt", "constraint");
}

#[test]
fn semantic_tokens_update_after_file_change() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let first = "def value : int := 1\n#check value : int\n";
    let second = "def value (x : int) : int := x\n#check value 1 : int\n";

    cache.update_fast(uri.clone(), Some(1), first.to_string());
    let first_tokens = cache.semantic_tokens(&uri).expect("first semantic tokens");
    let first_decoded = decode_semantic_tokens(first, &first_tokens);
    assert_token(&first_decoded, "value", "variable");

    cache.update_fast(uri.clone(), Some(2), second.to_string());
    let second_tokens = cache.semantic_tokens(&uri).expect("second semantic tokens");
    let second_decoded = decode_semantic_tokens(second, &second_tokens);
    assert_token(&second_decoded, "value", "function");
    assert_token(&second_decoded, "x", "parameter");
}

#[test]
fn semantic_tokens_highlight_comments_without_classifying_comment_text() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = r#"
-- def hidden : int := value
{- pub def also_hidden : int := 0 -}
def value : int := /- inline int value -/ 1
/-
def fake : int := value
-/
#check value : int
"#;

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "-- def hidden : int := value", "comment");
    assert_token(&decoded, "{- pub def also_hidden : int := 0 -}", "comment");
    assert_token(&decoded, "/- inline int value -/", "comment");
    assert_token(&decoded, "def fake : int := value", "comment");
    assert_token(&decoded, "value", "variable");
    assert_eq!(
        decoded
            .iter()
            .filter(|token| token.text == "value" && token.kind == "variable")
            .count(),
        2,
        "{decoded:#?}"
    );
}

#[test]
fn semantic_tokens_keep_classification_after_block_comment_in_declaration() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "def value : int := /- comment -/ 1\n#check value : int\n";

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "/- comment -/", "comment");
    assert_token(&decoded, "value", "variable");
    assert_token(&decoded, "int", "constraint");
}

#[test]
fn semantic_tokens_classify_metaprogramming_surface() {
    let mut cache = LspCache::new();
    let uri = lsp::Url::parse("file:///workspace/main.lig").unwrap();
    let source = "#check quote { 1 + 2 } : Expr\n#check Int 1 : Expr";

    cache.update_fast(uri.clone(), Some(1), source.to_string());
    let tokens = cache.semantic_tokens(&uri).expect("semantic tokens");
    let decoded = decode_semantic_tokens(source, &tokens);

    assert_token(&decoded, "quote", "keyword");
    assert_token(&decoded, "Expr", "constraint");
    assert_token(&decoded, "Int", "constructor");
}
