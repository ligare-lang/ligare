use ligare::checker::context::empty_ctx;
use ligare::core::classify::classify;
use ligare::core::pool::TermArena;
use ligare::core::syntax::{Tactic, Term, Universe};

#[test]
fn lit_int_is_data() {
    assert_eq!(
        classify(&empty_ctx(), &Term::LitInt(42)),
        Some(Universe::UData)
    );
}

#[test]
fn lit_bool_is_data() {
    assert_eq!(
        classify(&empty_ctx(), &Term::LitBool(true)),
        Some(Universe::UData)
    );
}

#[test]
fn lam_is_data() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Lam(&Term::Var(0))),
        Some(Universe::UData)
    );
}

#[test]
fn pi_is_prop() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::Pi("", &Term::Builtin("int"), &Term::Builtin("bool"))
        ),
        Some(Universe::UProp)
    );
}

#[test]
fn auto_proof_is_proof() {
    assert_eq!(
        classify(&empty_ctx(), &Term::AutoProof),
        Some(Universe::UProof)
    );
}

#[test]
fn universe_uprop_is_prop() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Universe(Universe::UProp)),
        Some(Universe::UProp)
    );
}

#[test]
fn int_builtin_is_prop() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Builtin("int")),
        Some(Universe::UProp)
    );
}

#[test]
fn and_is_prop() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Builtin("and")),
        Some(Universe::UProp)
    );
}

#[test]
fn annot_keeps_inner_universe() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::Annot(&Term::LitInt(5), &Term::Builtin("int"))
        ),
        Some(Universe::UData)
    );
}

#[test]
fn by_proof_keeps_inner_universe() {
    let bump = bumpalo::Bump::new();
    let arena = TermArena::new(&bump);
    let tactics = arena.alloc_slice(&[Tactic::Exact(arena.auto_proof())]);
    let term = arena.by_proof(Some(arena.lit_int(5)), tactics);
    assert_eq!(classify(&empty_ctx(), term), Some(Universe::UData));
}

#[test]
fn if_then_else_is_data() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::IfThenElse(&Term::LitBool(true), &Term::LitInt(1), &Term::LitInt(0))
        ),
        Some(Universe::UData)
    );
}

#[test]
fn func_is_data() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::Func(
                "f",
                &[("x", Some(&Term::Builtin("int")))],
                None,
                &Term::Var(0)
            )
        ),
        Some(Universe::UData)
    );
}

#[test]
fn let_is_body_universe() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::Let("x", &Term::LitInt(5), &Term::Var(0), None)
        ),
        None
    );
}

#[test]
fn unknown_builtin_is_nothing() {
    assert_eq!(classify(&empty_ctx(), &Term::Builtin("unknown")), None);
}
