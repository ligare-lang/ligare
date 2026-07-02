//! Parser tests for generic definitions and type applications.

use common::{leak_bump, s};
use ligare::core::pool::TermArena;
use ligare::core::syntax::Term;
use ligare::front::parser::parse_def_top;

mod common;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn parse_generic_id_definition() {
    let (b, arena) = a();
    let result = parse_def_top("def id (A : prop) (x : A) : A := x", b, &arena);
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, m_ret, body) = result.unwrap();
    assert_eq!(name, s(&arena, "id"));
    assert_eq!(params.len(), 2);
    // First param: A : prop
    assert_eq!(params[0].0, s(&arena, "A"));
    // Second param: x : A is still raw metadata on the def parameter list.
    assert_eq!(params[1].0, s(&arena, "x"));
    if let Some(ty) = params[1].1 {
        assert!(
            matches!(ty, Term::Builtin(name) | Term::Named(name) if *name == "A"),
            "x's type should be Named(\"A\") metadata, got: {:?}",
            ty
        );
    } else {
        panic!("x should have a type annotation");
    }
    // Return type should be A (Builtin)
    if let Some(ret) = m_ret {
        assert!(
            matches!(ret, Term::Builtin(name) | Term::Named(name) if *name == "A"),
            "Return type should be Named(\"A\") metadata, got: {:?}",
            ret
        );
    } else {
        panic!("should have return type");
    }
    assert_eq!(*body, Term::Named(s(&arena, "x")));
}

#[test]
fn parse_generic_two_type_params() {
    let (b, arena) = a();
    let result = parse_def_top(
        "def konst (A : prop) (B : prop) (x : A) (y : B) : A := x",
        b,
        &arena,
    );
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, _body) = result.unwrap();
    assert_eq!(name, s(&arena, "konst"));
    assert_eq!(params.len(), 4);
    // A : prop
    assert_eq!(params[0].0, s(&arena, "A"));
    // B : prop
    assert_eq!(params[1].0, s(&arena, "B"));
    // x : A metadata
    assert_eq!(params[2].0, s(&arena, "x"));
    if let Some(ty) = params[2].1 {
        assert!(
            matches!(ty, Term::Builtin(name) | Term::Named(name) if *name == "A"),
            "x's type should be Named(\"A\"), got: {:?}",
            ty
        );
    }
    // y : B metadata
    assert_eq!(params[3].0, s(&arena, "y"));
    if let Some(ty) = params[3].1 {
        assert!(
            matches!(ty, Term::Builtin(name) | Term::Named(name) if *name == "B"),
            "y's type should be Named(\"B\"), got: {:?}",
            ty
        );
    }
}

#[test]
fn parse_generic_with_prop_param() {
    let (b, arena) = a();
    let result = parse_def_top("def wrap (A : prop) (x : A) : A := x", b, &arena);
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, _body) = result.unwrap();
    assert_eq!(name, s(&arena, "wrap"));
    assert_eq!(params.len(), 2);
}

#[test]
fn parse_generic_enum_definition() {
    let (b, arena) = a();
    let result = parse_def_top(
        "def Option (A : prop) : prop := enum\n  | None\n  | Some of (val : A)\n",
        b,
        &arena,
    );
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, body) = result.unwrap();
    assert_eq!(name, s(&arena, "Option"));
    assert_eq!(params.len(), 1);
    assert_eq!(params[0].0, s(&arena, "A"));
    // Body should be EnumDef
    assert!(matches!(body, Term::EnumDef(..)));
}

#[test]
fn parse_generic_struct_definition() {
    let (b, arena) = a();
    let result = parse_def_top(
        "def Pair (A : prop) (B : prop) : prop := struct\n  fst : A\n  snd : B\n",
        b,
        &arena,
    );
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, body) = result.unwrap();
    assert_eq!(name, s(&arena, "Pair"));
    assert_eq!(params.len(), 2);
    assert!(matches!(body, Term::StructDef(..)));
}

#[test]
fn parse_generic_only_type_params_no_data() {
    let (b, arena) = a();
    let result = parse_def_top("def unit (A : prop) : int := 0", b, &arena);
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, _body) = result.unwrap();
    assert_eq!(name, s(&arena, "unit"));
    assert_eq!(params.len(), 1);
}

#[test]
fn parse_generic_raw_form() {
    let (b, arena) = a();
    let result = parse_def_top("def id (A : prop) (x : A) : A := x", b, &arena);
    let (_, params, m_ret, body) = result.unwrap();
    assert_eq!(*body, Term::Named(s(&arena, "x")));
    assert!(matches!(params[1].1, Some(Term::Named(name)) if *name == "A"));
    assert!(matches!(m_ret, Some(Term::Named(name)) if *name == "A"));
}
