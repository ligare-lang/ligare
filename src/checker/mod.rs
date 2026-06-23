pub mod builtin;
pub mod context;
pub mod erase;
pub mod infer;
pub mod prove;

use crate::checker::builtin::check_builtin;
use crate::checker::context::{ConstraintTable, Context, add_refine, empty_table, lookup_refine};
use crate::core::desugar::Desugarer;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Tactic, Term};
use crate::core::whnf::WhnfEvaluator;

/// The type checker — bundles arena, constraint table, and checking logic.
///
/// Maintains a constraint table that is mutated when refinement definitions
/// are encountered (via `add_refinement`).  Individual `check` calls may
/// create temporary table clones without mutating the persistent state.
pub struct TypeChecker<'bump> {
    pub(crate) arena: &'bump TermArena<'bump>,
    pub(crate) evaluator: WhnfEvaluator<'bump>,
    pub(crate) desugarer: Desugarer<'bump>,
    table: ConstraintTable<'bump>,
    /// Registry of union definitions: maps union name → UnionDef term
    pub(crate) union_table: Vec<(Name<'bump>, &'bump Term<'bump>)>,
    /// Registry of struct definitions: maps struct name → StructDef term
    pub(crate) struct_table: Vec<(Name<'bump>, &'bump Term<'bump>)>,
}

impl<'bump> TypeChecker<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self {
            arena,
            evaluator: WhnfEvaluator::new(arena),
            desugarer: Desugarer::new(arena),
            table: empty_table(),
            union_table: Vec::new(),
            struct_table: Vec::new(),
        }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Add a refinement definition to the persistent constraint table.
    pub fn add_refinement(
        &mut self,
        name: Name<'bump>,
        parent: &'bump Term<'bump>,
        predicate: &'bump Term<'bump>,
    ) {
        self.table.insert(0, (name, parent, predicate));
    }

    /// Add a union definition to the persistent union table.
    pub fn add_union(&mut self, name: Name<'bump>, def: &'bump Term<'bump>) {
        self.union_table.insert(0, (name, def));
    }

    /// Add a struct definition to the persistent struct table.
    pub fn add_struct(&mut self, name: Name<'bump>, def: &'bump Term<'bump>) {
        self.struct_table.insert(0, (name, def));
    }

    /// Look up a variant constructor name → (union_name, variant_index, field_specs).
    pub fn lookup_variant(
        &self,
        ctor_name: &str,
    ) -> Option<(
        Name<'bump>,
        usize,
        &'bump [(Name<'bump>, &'bump Term<'bump>)],
    )> {
        for (uname, udef) in &self.union_table {
            if let Term::UnionDef(_, variants) = udef {
                for (idx, (vname, fields)) in variants.iter().enumerate() {
                    if *vname == ctor_name {
                        return Some((*uname, idx, *fields));
                    }
                }
            }
        }
        None
    }

    /// Look up a union definition by name.
    pub fn lookup_union(&self, name: &str) -> Option<&'bump Term<'bump>> {
        self.union_table
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, def)| *def)
    }

    /// Look up a struct definition by name.
    pub fn lookup_struct(&self, name: &str) -> Option<&'bump Term<'bump>> {
        self.struct_table
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, def)| *def)
    }

    /// Look up a struct constructor name: `Foo.mk` → (struct_name, field_specs).
    /// Returns None if not a struct constructor.
    pub fn lookup_struct_ctor(
        &self,
        ctor_name: &str,
    ) -> Option<(Name<'bump>, &'bump [(Name<'bump>, &'bump Term<'bump>)])> {
        // Check if name ends with ".mk"
        if let Some(struct_name) = ctor_name.strip_suffix(".mk") {
            for (sname, sdef) in &self.struct_table {
                if *sname == struct_name {
                    if let Term::StructDef(_, fields) = sdef {
                        return Some((*sname, *fields));
                    }
                }
            }
        }
        None
    }

    /// Look up a struct field projector: `Foo.field` or `bar.field` → field index.
    /// Returns None if not a struct projector.
    pub fn lookup_struct_proj(&self, proj_name: &str) -> Option<usize> {
        if let Some(dot_pos) = proj_name.rfind('.') {
            let struct_name = &proj_name[..dot_pos];
            let field_name = &proj_name[dot_pos + 1..];
            for (sname, sdef) in &self.struct_table {
                if *sname == struct_name {
                    if let Term::StructDef(_, fields) = sdef {
                        return fields.iter().position(|(fnm, _)| *fnm == field_name);
                    }
                }
            }
        }
        None
    }

    /// Get a reference to the persistent constraint table.
    pub fn table(&self) -> &ConstraintTable<'bump> {
        &self.table
    }

    /// Check a term against a constraint.
    pub fn check(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let desugared = self.desugarer.desugar(term);
        match desugared {
            Term::Var(i) => self.check_var(ctx, *i, constraint),
            Term::Annot(t, c) => {
                if let (Term::Pi(..), Term::Pi(..)) = (c, constraint) {
                    self.check_pi_match(c, constraint)?;
                }
                self.check(ctx, t, c)?;
                self.check(ctx, t, constraint)
            }
            Term::ByProof(t_opt, tactics) => {
                let c_nf = self.evaluator.whnf(constraint)?;
                // Expand Builtin constraints (like `nat`) that are
                // actually refinement constraints in the table.
                let expanded = match c_nf {
                    Term::Builtin(name) => lookup_refine(name, &self.table)
                        .map(|(p, pr)| self.arena.refine(name, p, pr)),
                    _ => None,
                };
                let effective = expanded.unwrap_or(c_nf);
                match effective {
                    Term::Refine(_, parent, pred) => {
                        // Refinement: subject must satisfy parent, tactics prove predicate.
                        if let Some(subj) = t_opt {
                            self.check(ctx, subj, parent)?;
                            self.execute_tactics(ctx, Some(subj), pred, tactics)
                        } else {
                            // No subject — tactics build the whole proof.
                            let (proof, final_ctx) =
                                self.build_proof_from_tactics(ctx, None, constraint, tactics)?;
                            self.check(&final_ctx, proof, constraint)
                        }
                    }
                    _ => {
                        // Non-refinement: first try checking the subject
                        // directly (tactics are just evidence).  If that
                        // fails AND the tactics include intro/apply
                        // (which wrap the subject), fall back to building
                        // a proof from tactics.  Otherwise propagate the
                        // original error.
                        if let Some(subj) = t_opt {
                            if self.check(ctx, subj, constraint).is_ok() {
                                return Ok(());
                            }
                            let has_wrapping = tactics
                                .iter()
                                .any(|t| matches!(t, Tactic::Intro(_) | Tactic::Apply(_)));
                            if !has_wrapping {
                                return self.check(ctx, subj, constraint);
                            }
                        }
                        let (proof, final_ctx) =
                            self.build_proof_from_tactics(ctx, *t_opt, constraint, tactics)?;
                        self.check(&final_ctx, proof, constraint)
                    }
                }
            }
            Term::Refine(name, parent, p) => {
                let new_table = add_refine(name, parent, p, &self.table);
                let checker = Self::with_table(self.arena, &new_table);
                checker.check(ctx, constraint, constraint)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                self.check_if(ctx, cond, tbranch, fbranch, constraint)
            }
            Term::Let(_name, val, body, mconstr) => {
                self.check_let(ctx, val, body, *mconstr, constraint)
            }
            Term::Match(scrutinee, branches) => {
                self.check_match(ctx, scrutinee, branches, constraint)
            }
            Term::StructCons(sname, field_values) => {
                self.check_struct_cons(ctx, sname, field_values, constraint)
            }
            Term::StructProj(subject, idx) => {
                self.check_struct_proj(ctx, subject, *idx, constraint)
            }
            // Application: use the function's type rather than forcing
            // full evaluation (which would compute recursive calls).
            Term::App(f, a) => self.check_app(ctx, f, a, constraint),
            // A bare Builtin name may be a type (int, str, etc.) or a
            // refinement (nat).  If neither, check if it's a variant constructor
            // or a struct constructor / projector.
            Term::Builtin(name) => {
                if check_builtin(name).is_some() || lookup_refine(name, &self.table).is_some() {
                    self.check_by_constraint(ctx, desugared, constraint)
                } else if let Some((uname, idx, _)) = self.lookup_variant(name) {
                    // Zero-arg variant constructor → wrap as Variant
                    let variant_term = self.arena.variant(uname, idx, &[]);
                    self.check(ctx, variant_term, constraint)
                } else if self.lookup_struct_ctor(name).is_some() {
                    // Zero-arg struct constructor (struct with no fields)
                    let (sname, _fields) = self.lookup_struct_ctor(name).unwrap();
                    let sc = self.arena.struct_cons(sname, &[]);
                    self.check(ctx, sc, constraint)
                } else if self.lookup_struct_proj(name).is_some() {
                    // Struct projector used as a standalone function — we can't
                    // check it without a subject.  It's a data-level function.
                    Err(format!(
                        "Struct projector {} cannot be used as a value — apply it to a struct",
                        name
                    ))
                } else {
                    Err(format!("Undefined variable: {}", name))
                }
            }
            _ => self.check_by_constraint(ctx, desugared, constraint),
        }
    }

    /// Create a temporary checker with a different table (for sub-checks).
    pub(crate) fn with_table(
        arena: &'bump TermArena<'bump>,
        table: &ConstraintTable<'bump>,
    ) -> Self {
        Self {
            arena,
            evaluator: WhnfEvaluator::new(arena),
            desugarer: Desugarer::new(arena),
            table: table.clone(),
            union_table: Vec::new(),
            struct_table: Vec::new(),
        }
    }
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn check<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    term: &'bump Term<'bump>,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    let checker = TypeChecker {
        arena,
        evaluator: WhnfEvaluator::new(arena),
        desugarer: Desugarer::new(arena),
        table: table.clone(),
        union_table: Vec::new(),
        struct_table: Vec::new(),
    };
    checker.check(ctx, term, constraint)
}
