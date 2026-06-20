use std::collections::HashMap;
use std::sync::LazyLock;

use crate::config::{
    BUILTIN_AND, BUILTIN_BOOL, BUILTIN_DATA, BUILTIN_IMPLIES, BUILTIN_INT, BUILTIN_NOT, BUILTIN_OR,
    BUILTIN_PROOF, BUILTIN_THEOREM,
};
use crate::core::syntax::{Term, Universe};
use crate::pretty::PrettyPrinter;

pub type BuiltinChecker = fn(&Term<'_>) -> Result<(), String>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicKind {
    Conj,
    Disj,
    Vacuous,
}

pub struct BuiltinEntry {
    pub universe: Universe,
    pub checker: BuiltinChecker,
    pub logic_kind: Option<LogicKind>,
}

fn check_int(t: &Term<'_>) -> Result<(), String> {
    if matches!(t, Term::LitInt(_)) {
        Ok(())
    } else {
        Err(format!(
            "Expected an integer, but got {}",
            PrettyPrinter::pretty(t)
        ))
    }
}

fn check_bool(t: &Term<'_>) -> Result<(), String> {
    if matches!(t, Term::LitBool(_)) {
        Ok(())
    } else {
        Err(format!(
            "Expected a boolean, but got {}",
            PrettyPrinter::pretty(t)
        ))
    }
}

fn check_any(_t: &Term<'_>) -> Result<(), String> {
    Ok(())
}

fn entry(u: Universe, c: BuiltinChecker, lk: Option<LogicKind>) -> BuiltinEntry {
    BuiltinEntry {
        universe: u,
        checker: c,
        logic_kind: lk,
    }
}

static BUILTINS: LazyLock<HashMap<&'static str, BuiltinEntry>> = LazyLock::new(|| {
    HashMap::from([
        (BUILTIN_INT, entry(Universe::UProp, check_int, None)),
        (BUILTIN_BOOL, entry(Universe::UProp, check_bool, None)),
        (BUILTIN_DATA, entry(Universe::UProp, check_any, None)),
        (BUILTIN_THEOREM, entry(Universe::UTheorem, check_any, None)),
        (BUILTIN_PROOF, entry(Universe::UProof, check_any, None)),
        (
            BUILTIN_AND,
            entry(Universe::UProp, check_any, Some(LogicKind::Conj)),
        ),
        (
            BUILTIN_OR,
            entry(Universe::UProp, check_any, Some(LogicKind::Disj)),
        ),
        (
            BUILTIN_NOT,
            entry(Universe::UProp, check_any, Some(LogicKind::Vacuous)),
        ),
        (BUILTIN_IMPLIES, entry(Universe::UProp, check_any, None)),
    ])
});

pub fn classify_builtin(name: &str) -> Option<Universe> {
    BUILTINS.get(name).map(|e| e.universe)
}

pub fn check_builtin(name: &str) -> Option<BuiltinChecker> {
    BUILTINS.get(name).map(|e| e.checker)
}

pub fn logic_kind(name: &str) -> Option<LogicKind> {
    BUILTINS.get(name).and_then(|e| e.logic_kind)
}
