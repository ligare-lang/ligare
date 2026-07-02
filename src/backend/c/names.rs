//! Name resolution and collection for C code generation.
//!
//! `NameResolver` encapsulates C keyword escaping, lambda tree analysis,
//! and on-demand name collection — all as methods on a single object.

use crate::core::syntax::Term;
use crate::front::parser::TopLevel;
use std::collections::HashSet;

/// C keywords that conflict with Ligare identifiers.
const C_KEYWORDS: &[&str] = &[
    "auto",
    "break",
    "case",
    "char",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extern",
    "float",
    "for",
    "goto",
    "if",
    "int",
    "long",
    "register",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "struct",
    "switch",
    "typedef",
    "union",
    "unsigned",
    "void",
    "volatile",
    "while",
    "_Bool",
    "_Complex",
    "_Imaginary",
];

/// Resolves and escapes names for C output.
///
/// Stateless — all methods are pure transformations on input data.
#[derive(Debug, Clone, Default)]
pub struct NameResolver;

impl NameResolver {
    /// Create a new name resolver.
    pub fn new() -> Self {
        Self
    }

    /// Escape a name if it conflicts with a C keyword.
    pub fn escape(&self, name: &str) -> String {
        let collapsed = name.replace("::", "_");
        let mut out = String::with_capacity(collapsed.len());
        for ch in collapsed.chars() {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                out.push(ch);
            } else {
                out.push('_');
            }
        }
        if out.as_bytes().first().is_some_and(|b| b.is_ascii_digit()) {
            out.insert(0, '_');
        }
        if C_KEYWORDS.contains(&out.as_str()) {
            format!("_{out}")
        } else {
            out
        }
    }

    // ── Variable name generation (single source of truth) ──

    /// Generate an anonymous (lambda / De Bruijn) parameter name.
    pub fn anon_param(&self, index: usize) -> String {
        format!("arg_{index}")
    }

    /// Generate a scrutinee temporary variable name for match blocks.
    pub fn scrut_temp(&self, counter: u32) -> String {
        format!("_s{counter}")
    }

    /// Generate a result temporary variable name for match blocks.
    pub fn result_temp(&self, counter: u32) -> String {
        format!("_r{counter}")
    }

    // ── Lambda utilities ──

    /// Count the number of consecutive `Lam` wrappers on a term.
    pub fn count_lams(&self, term: &Term<'_>) -> usize {
        match term {
            Term::Lam(body) => 1 + self.count_lams(body),
            Term::Annot(inner, _) => self.count_lams(inner),
            _ => 0,
        }
    }

    /// Peel `n` layers of `Lam` (and `Annot`) from a term, returning the body.
    pub fn peel_lams<'a>(&self, term: &'a Term<'a>, n: usize) -> &'a Term<'a> {
        let mut t = term;
        let mut remaining = n;
        while remaining > 0 {
            match t {
                Term::Lam(body) => {
                    t = body;
                    remaining -= 1;
                }
                Term::Annot(inner, _) => {
                    t = inner;
                }
                _ => break,
            }
        }
        t
    }

    // ── Name collection for on-demand codegen ──

    /// Walk a set of Term trees and collect the names of all user-defined
    /// functions that are called (including transitive dependencies).
    /// Only returns names that appear in `raw_defs`.
    pub fn collect_called_names<'bump>(
        &self,
        outputs: &[&'bump Term<'bump>],
        raw_defs: &[TopLevel<'bump>],
    ) -> HashSet<String> {
        let def_names: HashSet<&str> = raw_defs
            .iter()
            .filter_map(|top| {
                if let TopLevel::TLDef(name, _, _, _, _) = top {
                    Some(*name)
                } else {
                    None
                }
            })
            .collect();
        let mut called = HashSet::new();
        // Seed with names found in output expressions.
        for term in outputs {
            self.collect_names_in_term(term, &def_names, &mut called);
        }
        // Transitive closure: also walk bodies of already-called functions.
        let mut changed = true;
        while changed {
            changed = false;
            let prev_len = called.len();
            for raw_def in raw_defs {
                if let TopLevel::TLDef(name, _, _, body, _) = raw_def
                    && called.contains(*name)
                {
                    self.collect_names_in_term(body, &def_names, &mut called);
                }
            }
            if called.len() > prev_len {
                changed = true;
            }
        }
        called
    }

    /// All definition names as a set (for library mode).
    pub fn all_def_names<'bump>(&self, raw_defs: &[TopLevel<'bump>]) -> HashSet<String> {
        raw_defs
            .iter()
            .filter_map(|top| {
                if let TopLevel::TLDef(name, _, _, _, _) = top {
                    Some(name.to_string())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn is_extern_name<'bump>(&self, name: &str, raw_defs: &[TopLevel<'bump>]) -> bool {
        raw_defs.iter().any(
            |top| matches!(top, TopLevel::TLExternDef(extern_name, ..) if *extern_name == name),
        )
    }

    /// Recursively walk a desugared term looking for global symbols that
    /// match known function definitions.
    /// nodes that match known function definitions.
    pub fn collect_names_in_term(
        &self,
        term: &Term<'_>,
        def_names: &HashSet<&str>,
        called: &mut HashSet<String>,
    ) {
        match term {
            Term::Builtin(name) | Term::Global(name) => {
                if def_names.contains(name) {
                    called.insert(name.to_string());
                }
            }
            Term::App(f, a) => {
                self.collect_names_in_term(f, def_names, called);
                self.collect_names_in_term(a, def_names, called);
            }
            Term::Implicit(inner) => {
                self.collect_names_in_term(inner, def_names, called);
            }
            Term::Lam(body) => {
                self.collect_names_in_term(body, def_names, called);
            }
            Term::Pi(_, a, b) => {
                self.collect_names_in_term(a, def_names, called);
                self.collect_names_in_term(b, def_names, called);
            }
            Term::Let(_, val, body, mconstr) => {
                self.collect_names_in_term(val, def_names, called);
                self.collect_names_in_term(body, def_names, called);
                if let Some(c) = mconstr {
                    self.collect_names_in_term(c, def_names, called);
                }
            }
            Term::Annot(t, c) => {
                self.collect_names_in_term(t, def_names, called);
                self.collect_names_in_term(c, def_names, called);
            }
            Term::IfThenElse(c, t, f) => {
                self.collect_names_in_term(c, def_names, called);
                self.collect_names_in_term(t, def_names, called);
                self.collect_names_in_term(f, def_names, called);
            }
            Term::Match(scrut, branches) => {
                self.collect_names_in_term(scrut, def_names, called);
                for (_, binds, body) in *branches {
                    for (_, bt) in *binds {
                        self.collect_names_in_term(bt, def_names, called);
                    }
                    self.collect_names_in_term(body, def_names, called);
                }
            }
            Term::Named(_) | Term::NamedLam(..) | Term::NamedMatch(..) | Term::Do(_) => {
                panic!("parser-level term reached C name collection before desugaring")
            }
            Term::Unsafe(inner) | Term::Pure(inner) => {
                self.collect_names_in_term(inner, def_names, called)
            }
            Term::StructCons(_, field_values) => {
                for v in *field_values {
                    self.collect_names_in_term(v, def_names, called);
                }
            }
            Term::StructProj(subj, _) => {
                self.collect_names_in_term(subj, def_names, called);
            }
            Term::Variant(_, _, payloads) => {
                for p in *payloads {
                    self.collect_names_in_term(p, def_names, called);
                }
            }
            Term::Refine(_, p, pred) => {
                self.collect_names_in_term(p, def_names, called);
                self.collect_names_in_term(pred, def_names, called);
            }
            Term::ByProof(subj_opt, tactics) => {
                if let Some(s) = subj_opt {
                    self.collect_names_in_term(s, def_names, called);
                }
                for tac in *tactics {
                    match tac {
                        crate::core::syntax::Tactic::Exact(t)
                        | crate::core::syntax::Tactic::Apply(t) => {
                            self.collect_names_in_term(t, def_names, called);
                        }
                        crate::core::syntax::Tactic::Have(_, t) => {
                            self.collect_names_in_term(t, def_names, called);
                        }
                        _ => {}
                    }
                }
            }
            // Leaf nodes: no children to recurse into.
            Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::LitStr(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::AutoProof
            | Term::RefParam
            | Term::UnionDef(..)
            | Term::StructDef(..) => {}
        }
    }
}
