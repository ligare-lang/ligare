use std::collections::HashMap;
use std::sync::LazyLock;

use crate::config::{
    BUILTIN_AND, BUILTIN_BOOL, BUILTIN_DATA, BUILTIN_IMPLIES, BUILTIN_INT, BUILTIN_NOT, BUILTIN_OR,
    BUILTIN_PROOF, BUILTIN_THEOREM,
};
use crate::core::syntax::{Term, Universe};
use crate::pretty::PrettyPrinter;

pub type BuiltinChecker = fn(&Term<'_>) -> Result<(), String>;

pub struct BuiltinEntry {
    pub universe: Universe,
    pub checker: BuiltinChecker,
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

/// Statically initialized builtin table via LazyLock, avoiding
/// repeated heap allocation on every lookup.
static BUILTINS: LazyLock<HashMap<&'static str, BuiltinEntry>> = LazyLock::new(|| {
    HashMap::from([
        (
            BUILTIN_INT,
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_int,
            },
        ),
        (
            BUILTIN_BOOL,
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_bool,
            },
        ),
        (
            BUILTIN_DATA,
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
        (
            BUILTIN_THEOREM,
            BuiltinEntry {
                universe: Universe::UTheorem,
                checker: check_any,
            },
        ),
        (
            BUILTIN_PROOF,
            BuiltinEntry {
                universe: Universe::UProof,
                checker: check_any,
            },
        ),
        (
            BUILTIN_AND,
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
        (
            BUILTIN_OR,
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
        (
            BUILTIN_NOT,
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
        (
            BUILTIN_IMPLIES,
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
    ])
});

pub fn classify_builtin(name: &str) -> Option<Universe> {
    BUILTINS.get(name).map(|e| e.universe)
}

pub fn check_builtin(name: &str) -> Option<BuiltinChecker> {
    BUILTINS.get(name).map(|e| e.checker)
}
