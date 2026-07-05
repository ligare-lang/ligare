use super::*;
use crate::core::pool::TermArena;
use crate::core::syntax::PrimOp;

fn setup() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(bumpalo::Bump::new()));
    (b, TermArena::new(b))
}

#[test]
fn let_destructuring_ast() {
    let (bump, arena) = setup();
    let term = parse_expr_top("let Point{x, y} := p in x + y", bump, &arena)
        .expect("parse should succeed");

    match term {
        Term::Let(name_x, val_x, body, None) => {
            assert_eq!(name_x, &"x");
            match val_x {
                Term::App(proj_x, arg_x) => {
                    assert_eq!(**proj_x, Term::Named("Point.x"));
                    assert_eq!(**arg_x, Term::Named("p"));
                }
                other => panic!("expected App for x projection, got {:?}", other),
            }
            match body {
                Term::Let(name_y, val_y, inner_body, None) => {
                    assert_eq!(name_y, &"y");
                    match val_y {
                        Term::App(proj_y, arg_y) => {
                            assert_eq!(**proj_y, Term::Named("Point.y"));
                            assert_eq!(**arg_y, Term::Named("p"));
                        }
                        other => panic!("expected App for y projection, got {:?}", other),
                    }
                    match inner_body {
                        Term::App(op_app, rhs) => match op_app {
                            Term::App(op, lhs) => {
                                assert_eq!(**op, Term::PrimOp(PrimOp::Add));
                                assert_eq!(**lhs, Term::Named("x"));
                                assert_eq!(**rhs, Term::Named("y"));
                            }
                            other => panic!("expected App(PrimOp(Add), lhs), got {:?}", other),
                        },
                        other => panic!("expected App for addition, got {:?}", other),
                    }
                }
                other => panic!("expected Let for y binding, got {:?}", other),
            }
        }
        other => panic!("expected Let at top, got {:?}", other),
    }
}

#[test]
fn struct_definition_ast() {
    let (bump, arena) = setup();
    let (name, params, m_ret, body) =
        parse_def_top("def Foo : prop := struct a : int b : str", bump, &arena)
            .expect("parse should succeed");

    assert_eq!(name, "Foo");
    assert!(params.is_empty());
    assert_eq!(m_ret.copied(), Some(Term::Builtin("prop")));

    match body {
        Term::StructDef(struct_name, fields) => {
            assert_eq!(struct_name, &"Foo");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "a");
            assert_eq!(*fields[0].1, Term::Builtin("int"));
            assert_eq!(fields[1].0, "b");
            assert_eq!(*fields[1].1, Term::Builtin("str"));
        }
        other => panic!("expected StructDef, got {:?}", other),
    }
}

#[test]
fn lambda_application_ast() {
    let (bump, arena) = setup();
    let term = parse_expr_top("fun x => x + 1", bump, &arena).expect("parse should succeed");

    match term {
        Term::Annot(inner, constraint) => {
            assert!(matches!(**constraint, Term::Pi(..)));
            let Term::NamedLam(name, body) = inner else {
                panic!("expected NamedLam inside fun annotation, got {:?}", inner);
            };
            assert_eq!(name, &"x");
            match body {
                Term::App(op_app, rhs) => {
                    match op_app {
                        Term::App(op, lhs) => {
                            assert_eq!(**op, Term::PrimOp(PrimOp::Add));
                            assert_eq!(**lhs, Term::Named("x"));
                        }
                        other => panic!("expected App(PrimOp(Add), lhs), got {:?}", other),
                    }
                    assert_eq!(**rhs, Term::LitInt(1));
                }
                other => panic!("expected App in lam body, got {:?}", other),
            }
        }
        other => panic!("expected Annot for fun lambda, got {:?}", other),
    }
}

#[test]
fn if_expression_ast() {
    let (bump, arena) = setup();
    let term = parse_expr_top("if true then 1 else 0", bump, &arena).expect("parse should succeed");

    match term {
        Term::IfThenElse(cond, tbranch, fbranch) => {
            assert_eq!(**cond, Term::LitBool(true));
            assert_eq!(**tbranch, Term::LitInt(1));
            assert_eq!(**fbranch, Term::LitInt(0));
        }
        other => panic!("expected IfThenElse, got {:?}", other),
    }
}

#[test]
fn match_expression_ast() {
    let (bump, arena) = setup();
    let term = parse_expr_top("match x with | A => 1 | B => 2", bump, &arena)
        .expect("parse should succeed");

    match term {
        Term::NamedMatch(scrutinee, branches) => {
            assert_eq!(**scrutinee, Term::Named("x"));
            assert_eq!(branches.len(), 2);

            let (variant0, binds0, body0) = &branches[0];
            assert_eq!(*variant0, "A");
            assert!(binds0.is_empty());
            assert_eq!(**body0, Term::LitInt(1));

            let (variant1, binds1, body1) = &branches[1];
            assert_eq!(*variant1, "B");
            assert!(binds1.is_empty());
            assert_eq!(**body1, Term::LitInt(2));
        }
        other => panic!("expected NamedMatch, got {:?}", other),
    }
}

#[test]
fn dotted_name_ast() {
    let (bump, arena) = setup();
    let term = parse_expr_top("Foo.bar", bump, &arena).expect("parse should succeed");
    assert_eq!(*term, Term::Named("Foo.bar"));
}
