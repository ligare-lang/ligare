//! Builtin type registry.
//!
//! `BuiltinRegistry` maps builtin names (int, bool, str, data, prop, etc.)
//! to their universes, checkers, and logic kinds.  It is constructed at
//! startup and injected into `TypeChecker` — no global state.

use std::collections::HashMap;

use crate::config::{
    BUILTIN_AND, BUILTIN_BOOL, BUILTIN_C_INT, BUILTIN_C_UINT, BUILTIN_DATA, BUILTIN_I8,
    BUILTIN_I16, BUILTIN_I32, BUILTIN_I64, BUILTIN_IMPLIES, BUILTIN_INT, BUILTIN_IO, BUILTIN_NOT,
    BUILTIN_OR, BUILTIN_PROOF, BUILTIN_PROP, BUILTIN_PTR, BUILTIN_STR, BUILTIN_THEOREM, BUILTIN_U8,
    BUILTIN_U16, BUILTIN_U32, BUILTIN_U64, BUILTIN_UNIT, canonical_builtin_name, is_builtin_name,
};
use crate::core::syntax::{Term, Universe};
use crate::diagnostic::Diagnostic;
use crate::pretty::PrettyPrinter;

pub type BuiltinChecker = fn(&Term<'_>) -> Result<(), Diagnostic>;

pub const BUILTIN_CONSTRAINT_NAMES: &[&str] = &[
    BUILTIN_INT,
    BUILTIN_BOOL,
    BUILTIN_STR,
    BUILTIN_IO,
    BUILTIN_UNIT,
    BUILTIN_DATA,
    BUILTIN_PROP,
    BUILTIN_THEOREM,
    BUILTIN_PROOF,
    BUILTIN_AND,
    BUILTIN_OR,
    BUILTIN_NOT,
    BUILTIN_IMPLIES,
    BUILTIN_I8,
    BUILTIN_I16,
    BUILTIN_I32,
    BUILTIN_I64,
    BUILTIN_U8,
    BUILTIN_U16,
    BUILTIN_U32,
    BUILTIN_U64,
    BUILTIN_C_INT,
    BUILTIN_C_UINT,
    BUILTIN_PTR,
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicKind {
    Conj,
    Disj,
    Vacuous,
}

#[derive(Debug, Clone, Copy)]
pub struct BuiltinEntry {
    pub universe: Universe,
    pub checker: BuiltinChecker,
    pub logic_kind: Option<LogicKind>,
}

fn check_int(t: &Term<'_>) -> Result<(), Diagnostic> {
    if matches!(t, Term::LitInt(_)) {
        Ok(())
    } else {
        Err(Diagnostic::new(format!(
            "expected int, got {}",
            PrettyPrinter::pretty(t)
        )))
    }
}

fn check_bool(t: &Term<'_>) -> Result<(), Diagnostic> {
    if matches!(t, Term::LitBool(_)) {
        Ok(())
    } else {
        Err(Diagnostic::new(format!(
            "expected bool, got {}",
            PrettyPrinter::pretty(t)
        )))
    }
}

fn check_str(t: &Term<'_>) -> Result<(), Diagnostic> {
    match t {
        Term::LitStr(_) => Ok(()),
        _ => Err(Diagnostic::new(format!(
            "expected str, got {}",
            PrettyPrinter::pretty(t)
        ))),
    }
}

fn check_unit(t: &Term<'_>) -> Result<(), Diagnostic> {
    match t {
        Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_UNIT) => Ok(()),
        _ => Err(Diagnostic::new(format!(
            "expected (), got {}",
            PrettyPrinter::pretty(t)
        ))),
    }
}

fn check_any(_t: &Term<'_>) -> Result<(), Diagnostic> {
    Ok(())
}

fn entry(u: Universe, c: BuiltinChecker, lk: Option<LogicKind>) -> BuiltinEntry {
    BuiltinEntry {
        universe: u,
        checker: c,
        logic_kind: lk,
    }
}

/// Registry of builtin types and logic operators.
///
/// Owned by `TypeChecker`; constructed once at startup.  Semantic queries can
/// access a shared reference for builtin universe lookup.
#[derive(Debug, Clone)]
pub struct BuiltinRegistry {
    table: HashMap<&'static str, BuiltinEntry>,
}

impl BuiltinRegistry {
    /// Create the standard builtin registry.
    pub fn new() -> Self {
        Self {
            table: HashMap::from([
                (BUILTIN_INT, entry(Universe::UProp, check_int, None)),
                (BUILTIN_I8, entry(Universe::UProp, check_int, None)),
                (BUILTIN_I16, entry(Universe::UProp, check_int, None)),
                (BUILTIN_I32, entry(Universe::UProp, check_int, None)),
                (BUILTIN_I64, entry(Universe::UProp, check_int, None)),
                (BUILTIN_U8, entry(Universe::UProp, check_int, None)),
                (BUILTIN_U16, entry(Universe::UProp, check_int, None)),
                (BUILTIN_U32, entry(Universe::UProp, check_int, None)),
                (BUILTIN_U64, entry(Universe::UProp, check_int, None)),
                (BUILTIN_C_INT, entry(Universe::UProp, check_int, None)),
                (BUILTIN_C_UINT, entry(Universe::UProp, check_int, None)),
                (BUILTIN_PTR, entry(Universe::UProp, check_any, None)),
                (BUILTIN_BOOL, entry(Universe::UProp, check_bool, None)),
                (BUILTIN_STR, entry(Universe::UProp, check_str, None)),
                (BUILTIN_IO, entry(Universe::UProp, check_any, None)),
                (BUILTIN_UNIT, entry(Universe::UProp, check_unit, None)),
                (BUILTIN_DATA, entry(Universe::UProp, check_any, None)),
                (BUILTIN_PROP, entry(Universe::UProp, check_any, None)),
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
            ]),
        }
    }

    /// Return the universe associated with a builtin name.
    pub fn universe_of(&self, name: &str) -> Option<Universe> {
        self.table
            .get(canonical_builtin_name(name))
            .map(|e| e.universe)
    }

    /// Get the checker function for a builtin name.
    pub fn checker(&self, name: &str) -> Option<BuiltinChecker> {
        self.table
            .get(canonical_builtin_name(name))
            .map(|e| e.checker)
    }

    /// Get the logic kind for a builtin name.
    pub fn logic_kind(&self, name: &str) -> Option<LogicKind> {
        self.table
            .get(canonical_builtin_name(name))
            .and_then(|e| e.logic_kind)
    }
}

impl Default for BuiltinRegistry {
    fn default() -> Self {
        Self::new()
    }
}
