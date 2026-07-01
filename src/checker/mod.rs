pub mod builtin;
pub mod context;
pub mod erase;
pub mod infer;
pub mod prove;

use crate::checker::builtin::BuiltinRegistry;
use crate::checker::context::{ConstraintTable, Context, add_refine, empty_table, lookup_refine};
use crate::core::debruijn::Desugarer;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Tactic, Term};
use crate::diagnostic::Diagnostic;

/// Result of looking up a variant constructor: (union_name, variant_index, field_specs).
type VariantInfo<'bump> = (
    Name<'bump>,
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
);
use crate::core::whnf::WhnfEvaluator;

/// Constraint checker — bundles arena, constraint table, and checking logic.
///
/// Maintains a constraint table that is mutated when refinement definitions
/// are encountered (via `add_refinement`).  Individual `check` calls may
/// create temporary table clones without mutating the persistent state.
pub struct TypeChecker<'bump> {
    pub(crate) arena: &'bump TermArena<'bump>,
    pub(crate) evaluator: WhnfEvaluator<'bump>,
    pub(crate) builtins: BuiltinRegistry,
    table: ConstraintTable<'bump>,
    /// Registry of union definitions: maps union name → (UnionDef term, param_names)
    pub(crate) union_table: Vec<(Name<'bump>, &'bump Term<'bump>, &'bump [Name<'bump>])>,
    /// Registry of struct definitions: maps struct name → (StructDef term, param_names)
    pub(crate) struct_table: Vec<(Name<'bump>, &'bump Term<'bump>, &'bump [Name<'bump>])>,
}

impl<'bump> TypeChecker<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self {
            arena,
            evaluator: WhnfEvaluator::new(arena),
            builtins: BuiltinRegistry::new(),
            table: empty_table(),
            union_table: Vec::new(),
            struct_table: Vec::new(),
        }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    pub fn builtins(&self) -> &BuiltinRegistry {
        &self.builtins
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
    pub fn add_union(
        &mut self,
        name: Name<'bump>,
        def: &'bump Term<'bump>,
        type_params: &'bump [Name<'bump>],
    ) {
        self.union_table.insert(0, (name, def, type_params));
    }

    /// Add a struct definition to the persistent struct table.
    pub fn add_struct(
        &mut self,
        name: Name<'bump>,
        def: &'bump Term<'bump>,
        type_params: &'bump [Name<'bump>],
    ) {
        self.struct_table.insert(0, (name, def, type_params));
    }

    /// Look up a variant constructor name → (union_name, variant_index, field_specs).
    pub fn lookup_variant(&self, ctor_name: &str) -> Option<VariantInfo<'bump>> {
        for (uname, udef, _) in &self.union_table {
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

    pub(crate) fn desugar_with_context(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let resolver = |name: &str| self.lookup_variant(name);
        Desugarer::new(self.arena)
            .try_desugar_with_variant_resolver(term, &resolver)
            .map_err(Diagnostic::new)
    }

    pub(crate) fn desugar_with_names_context(
        &self,
        term: &'bump Term<'bump>,
        env: &[&'bump str],
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let resolver = |name: &str| self.lookup_variant(name);
        Desugarer::new(self.arena)
            .try_desugar_with_names_and_variant_resolver(term, env, &resolver)
            .map_err(Diagnostic::new)
    }

    /// Look up a union definition by name.
    pub fn lookup_union(&self, name: &str) -> Option<(&'bump Term<'bump>, &'bump [Name<'bump>])> {
        self.union_table
            .iter()
            .find(|(n, _, _)| *n == name)
            .map(|(_, def, params)| (*def, *params))
    }

    /// Look up a struct definition by name.
    pub fn lookup_struct(&self, name: &str) -> Option<(&'bump Term<'bump>, &'bump [Name<'bump>])> {
        self.struct_table
            .iter()
            .find(|(n, _, _)| *n == name)
            .map(|(_, def, params)| (*def, *params))
    }

    /// Look up a struct constructor name: `Foo.mk` → (struct_name, field_specs).
    /// Returns None if not a struct constructor.
    pub fn lookup_struct_ctor(
        &self,
        ctor_name: &str,
    ) -> Option<(Name<'bump>, &'bump [(Name<'bump>, &'bump Term<'bump>)])> {
        // Check if name ends with ".mk"
        if let Some(struct_name) = ctor_name.strip_suffix(".mk") {
            for (sname, sdef, _) in &self.struct_table {
                if *sname == struct_name
                    && let Term::StructDef(_, fields) = sdef
                {
                    return Some((*sname, *fields));
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
            for (sname, sdef, _) in &self.struct_table {
                if *sname == struct_name
                    && let Term::StructDef(_, fields) = sdef
                {
                    return fields.iter().position(|(fnm, _)| *fnm == field_name);
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
    ) -> Result<(), Diagnostic> {
        let desugared = self.desugar_with_context(term)?;
        match desugared {
            Term::Var(i) => self.check_var(ctx, *i, constraint),
            Term::Annot(t, c) => {
                if let (Term::Pi(..), Term::Pi(..)) = (c, constraint) {
                    self.check_pi_match(c, constraint)?;
                    return self.check(ctx, t, constraint);
                }
                self.check(ctx, t, c)?;
                self.check(ctx, t, constraint)
            }
            Term::ByProof(t_opt, tactics) => {
                let c_nf = self.evaluator.whnf(constraint)?;
                // Expand Builtin constraints (like `Nat`) that are
                // actually refinement constraints in the table.
                let expanded = match c_nf {
                    Term::Builtin(name) | Term::Global(name) => lookup_refine(name, &self.table)
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
            Term::Do(_) => Err(Diagnostic::new(
                "`do` block can only appear in a function returning an effect constraint",
            )),
            Term::StructCons(sname, field_values) => {
                self.check_struct_cons(ctx, sname, field_values, constraint)
            }
            Term::Variant(uname, idx, payloads) => {
                self.check_variant(ctx, uname, *idx, payloads, constraint)
            }
            Term::StructProj(subject, idx) => {
                self.check_struct_proj(ctx, subject, *idx, constraint)
            }
            // Application: use the term's Pi constraint rather than forcing
            // full evaluation (which would compute recursive calls).
            Term::App(f, a) => self.check_app(ctx, f, a, constraint),
            // A bare Builtin/Named name may be a constraint (int, str, etc.) or a
            // refinement (Nat).  If neither, check if it's a variant constructor
            // or a struct constructor / projector.
            Term::Builtin(name) | Term::Global(name) => {
                if self.builtins.checker(name).is_some()
                    || lookup_refine(name, &self.table).is_some()
                {
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
                } else if self.is_struct_projector_name(name) {
                    // Struct projector used as a standalone function, or an
                    // unknown field on a known struct.
                    if self.lookup_struct_proj(name).is_some() {
                        Err(Diagnostic::new(format!(
                            "{} must be applied to a struct",
                            name
                        )))
                    } else {
                        Err(Diagnostic::new(format!(
                            "unknown struct field projector: {}",
                            name
                        )))
                    }
                } else {
                    Err(Diagnostic::new(format!("unbound: {}", name)))
                }
            }
            _ => self.check_by_constraint(ctx, desugared, constraint),
        }
    }

    fn is_struct_projector_name(&self, name: &str) -> bool {
        let Some((struct_name, _field_name)) = name.rsplit_once('.') else {
            return false;
        };
        self.lookup_struct(struct_name).is_some()
    }

    /// Create a temporary checker with a different table (for sub-checks).
    pub(crate) fn with_table(
        arena: &'bump TermArena<'bump>,
        table: &ConstraintTable<'bump>,
    ) -> Self {
        Self {
            arena,
            evaluator: WhnfEvaluator::new(arena),
            builtins: BuiltinRegistry::new(),
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
) -> Result<(), Diagnostic> {
    let checker = TypeChecker {
        arena,
        evaluator: WhnfEvaluator::new(arena),
        builtins: BuiltinRegistry::new(),
        table: table.clone(),
        union_table: Vec::new(),
        struct_table: Vec::new(),
    };
    checker.check(ctx, term, constraint)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::checker::context::empty_ctx;
    use crate::core::syntax::Universe;
    use bumpalo::Bump;

    fn a() -> (&'static Bump, &'static TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        let arena = Box::leak(Box::new(TermArena::new(b)));
        (b, arena)
    }

    fn checker(arena: &'static TermArena<'static>) -> TypeChecker<'static> {
        TypeChecker::new(arena)
    }

    // ── basic checks ──

    #[test]
    fn int_literal_checks_as_int() {
        let (_b, arena) = a();
        let chk = checker(arena);
        let t = arena.lit_int(42);
        let c = arena.builtin(arena.alloc_str("int"));
        assert!(chk.check(&empty_ctx(), t, c).is_ok());
    }

    #[test]
    fn int_literal_fails_against_bool() {
        let (_b, arena) = a();
        let chk = checker(arena);
        let t = arena.lit_int(42);
        let c = arena.builtin(arena.alloc_str("bool"));
        assert!(chk.check(&empty_ctx(), t, c).is_err());
    }

    #[test]
    fn bool_literal_checks_as_bool() {
        let (_b, arena) = a();
        let chk = checker(arena);
        let t = arena.lit_bool(true);
        let c = arena.builtin(arena.alloc_str("bool"));
        assert!(chk.check(&empty_ctx(), t, c).is_ok());
    }

    #[test]
    fn literal_checks_as_data_universe() {
        let (_b, arena) = a();
        let chk = checker(arena);
        let t = arena.lit_int(5);
        let c = arena.universe(Universe::UData);
        assert!(chk.check(&empty_ctx(), t, c).is_ok());
    }

    #[test]
    fn lam_checks_as_pi() {
        let (_b, arena) = a();
        let chk = checker(arena);
        let lam = arena.lam(arena.lit_int(5));
        let pi = arena.pi(
            arena.alloc_str(""),
            arena.builtin(arena.alloc_str("int")),
            arena.builtin(arena.alloc_str("int")),
        );
        assert!(chk.check(&empty_ctx(), lam, pi).is_ok());
    }

    #[test]
    fn app_of_lam_checks() {
        let (_b, arena) = a();
        let chk = checker(arena);
        // id = λx. x : int → int
        let body = arena.annot(
            arena.lam(arena.var(0)),
            arena.pi(
                arena.alloc_str(""),
                arena.builtin(arena.alloc_str("int")),
                arena.builtin(arena.alloc_str("int")),
            ),
        );
        // id 5 should be int
        let app = arena.app(body, arena.lit_int(5));
        let c = arena.builtin(arena.alloc_str("int"));
        assert!(chk.check(&empty_ctx(), app, c).is_ok());
    }
}
