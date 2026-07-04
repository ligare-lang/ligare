pub mod builtin;
pub mod context;
pub mod erase;
pub mod infer;
pub mod prove;

use crate::checker::builtin::BuiltinRegistry;
use crate::checker::context::{ConstraintTable, Context, add_refine, empty_table, lookup_refine};
use crate::config::{BUILTIN_IO, is_builtin_name};
use crate::core::debruijn::Desugarer;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Tactic, Term};
use crate::diagnostic::Diagnostic;

/// Result of looking up a variant constructor: (enum_name, variant_index, field_specs).
type VariantInfo<'bump> = (
    Name<'bump>,
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
);
#[derive(Debug, Clone, Copy)]
pub struct MethodInstance<'bump> {
    pub name: Name<'bump>,
    pub interface_name: Name<'bump>,
    pub value: &'bump Term<'bump>,
}
use crate::core::whnf::WhnfEvaluator;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckMode {
    Full,
    Fast,
}

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
    /// Registry of enum definitions: maps enum name → (EnumDef term, param_names)
    pub(crate) enum_table: Vec<(Name<'bump>, &'bump Term<'bump>, &'bump [Name<'bump>])>,
    /// Registry of struct definitions: maps struct name → (StructDef term, param_names)
    pub(crate) struct_table: Vec<(Name<'bump>, &'bump Term<'bump>, &'bump [Name<'bump>])>,
    /// External C function signatures.
    pub(crate) extern_table: Vec<(Name<'bump>, &'bump Term<'bump>)>,
    /// Compile-time implicit instances: name, constraint, value.
    pub(crate) instance_table: Vec<(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>)>,
    /// Whether the current check is inside an explicit unsafe expression.
    pub(crate) unsafe_depth: usize,
    mode: CheckMode,
}

impl<'bump> TypeChecker<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self {
            arena,
            evaluator: WhnfEvaluator::new(arena),
            builtins: BuiltinRegistry::new(),
            table: empty_table(),
            enum_table: Vec::new(),
            struct_table: Vec::new(),
            extern_table: Vec::new(),
            instance_table: Vec::new(),
            unsafe_depth: 0,
            mode: CheckMode::Full,
        }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    pub fn builtins(&self) -> &BuiltinRegistry {
        &self.builtins
    }

    pub fn set_mode(&mut self, mode: CheckMode) {
        self.mode = mode;
    }

    pub fn mode(&self) -> CheckMode {
        self.mode
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

    /// Add an enum definition to the persistent enum table.
    pub fn add_enum(
        &mut self,
        name: Name<'bump>,
        def: &'bump Term<'bump>,
        type_params: &'bump [Name<'bump>],
    ) {
        self.enum_table.insert(0, (name, def, type_params));
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

    /// Add an external C function signature.
    pub fn add_extern(&mut self, name: Name<'bump>, signature: &'bump Term<'bump>) {
        self.extern_table.insert(0, (name, signature));
    }

    pub fn add_instance(
        &mut self,
        name: Name<'bump>,
        constraint: &'bump Term<'bump>,
        value: &'bump Term<'bump>,
    ) {
        self.instance_table.insert(0, (name, constraint, value));
    }

    pub fn lookup_instance(
        &self,
        constraint: &'bump Term<'bump>,
    ) -> Result<Option<(Name<'bump>, &'bump Term<'bump>)>, Diagnostic> {
        let wanted = self.evaluator.whnf(Self::implicit_inner(constraint))?;
        for (name, have, value) in &self.instance_table {
            let have = self.evaluator.whnf(Self::implicit_inner(have))?;
            if self.constraint_equiv(have, wanted) {
                return Ok(Some((*name, *value)));
            }
        }
        Ok(None)
    }

    pub fn lookup_method_instances(
        &self,
        method: &str,
        receiver_constraint: &'bump Term<'bump>,
    ) -> Vec<MethodInstance<'bump>> {
        let mut matches = Vec::new();
        for (name, have, value) in &self.instance_table {
            if let Some(candidate) =
                self.lookup_method_on_instance(method, receiver_constraint, *name, have, value)
            {
                matches.push(candidate);
            }
        }
        matches
    }

    pub fn lookup_method_on_instance(
        &self,
        method: &str,
        receiver_constraint: &'bump Term<'bump>,
        instance_name: Name<'bump>,
        instance_constraint: &'bump Term<'bump>,
        instance_value: &'bump Term<'bump>,
    ) -> Option<MethodInstance<'bump>> {
        let have = self
            .evaluator
            .whnf(Self::implicit_inner(instance_constraint))
            .ok()?;
        let (interface_name, type_args) = self.constraint_head_and_args(have)?;
        let (Term::StructDef(_, fields), type_params) = self.lookup_struct(interface_name)? else {
            return None;
        };
        let (_, field_constraint) = fields.iter().find(|(field, _)| *field == method)?;
        let field_constraint = if type_args.len() == type_params.len() {
            self.replace_type_args(field_constraint, &type_args)
        } else {
            *field_constraint
        };
        let first_domain = Self::first_pi_domain(field_constraint)?;
        self.check_domain_match(first_domain, receiver_constraint)
            .is_ok()
            .then_some(MethodInstance {
                name: instance_name,
                interface_name,
                value: instance_value,
            })
    }

    fn first_pi_domain(term: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        match term {
            Term::Pi(_, domain, _) => Some(*domain),
            Term::Implicit(inner) => Self::first_pi_domain(inner),
            Term::Annot(_, constraint) => Self::first_pi_domain(constraint),
            _ => None,
        }
    }

    fn constraint_head_and_args(
        &self,
        term: &'bump Term<'bump>,
    ) -> Option<(Name<'bump>, Vec<&'bump Term<'bump>>)> {
        let mut args = Vec::new();
        let mut current = term;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        match current {
            Term::Builtin(name) | Term::Global(name) => Some((*name, args)),
            Term::StructDef(name, _) => Some((*name, args)),
            _ => None,
        }
    }

    fn replace_type_args(
        &self,
        term: &'bump Term<'bump>,
        type_args: &[&'bump Term<'bump>],
    ) -> &'bump Term<'bump> {
        match term {
            Term::Var(i) if *i < type_args.len() => type_args[type_args.len() - 1 - *i],
            Term::App(f, a) => self.arena.app(
                self.replace_type_args(f, type_args),
                self.replace_type_args(a, type_args),
            ),
            Term::Implicit(inner) => self
                .arena
                .implicit(self.replace_type_args(inner, type_args)),
            Term::Pi(name, a, b) => self.arena.pi(
                name,
                self.replace_type_args(a, type_args),
                self.replace_type_args(b, type_args),
            ),
            Term::Annot(inner, c) => self.arena.annot(
                self.replace_type_args(inner, type_args),
                self.replace_type_args(c, type_args),
            ),
            _ => term,
        }
    }

    pub(crate) fn implicit_inner(t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Implicit(inner) => inner,
            _ => t,
        }
    }

    pub(crate) fn is_implicit_constraint(t: &Term<'_>) -> bool {
        matches!(t, Term::Implicit(_))
    }

    pub(crate) fn lookup_extern(&self, name: &str) -> Option<&'bump Term<'bump>> {
        self.extern_table
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, sig)| *sig)
    }

    /// Look up a variant constructor name → (enum_name, variant_index, field_specs).
    pub fn lookup_variant(&self, ctor_name: &str) -> Option<VariantInfo<'bump>> {
        for (uname, udef, _) in &self.enum_table {
            if let Term::EnumDef(_, variants) = udef {
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

    /// Look up an enum definition by name.
    pub fn lookup_enum(&self, name: &str) -> Option<(&'bump Term<'bump>, &'bump [Name<'bump>])> {
        self.enum_table
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
            Term::Unsafe(inner) => {
                let mut checker = self.clone_for_unsafe();
                checker.unsafe_depth += 1;
                checker.check(ctx, inner, constraint)
            }
            Term::Pure(inner) => self.check_pure(ctx, inner, constraint),
            Term::Var(i) => self.check_var(ctx, *i, constraint),
            Term::Annot(t, c) => {
                if matches!(t, Term::Builtin(_) | Term::Global(_)) && matches!(c, Term::Pi(..)) {
                    return self.check_domain_match(c, constraint);
                }
                if let (Term::Pi(..), Term::Pi(..)) = (c, constraint) {
                    self.check_pi_match(c, constraint)?;
                    return self.check(ctx, t, constraint);
                }
                self.check(ctx, t, c)?;
                self.check(ctx, t, constraint)
            }
            Term::ByProof(t_opt, tactics) => {
                if self.mode == CheckMode::Fast {
                    return self.check_by_proof_fast(ctx, *t_opt, constraint);
                }
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
            Term::MethodCall(..) => Err(Diagnostic::new(
                "method call reached checker before resolution",
            )),
            // Application: use the term's Pi constraint rather than forcing
            // full evaluation (which would compute recursive calls).
            Term::App(f, a) => self.check_app(ctx, f, a, constraint),
            // A bare Builtin/Named name may be a constraint (int, str, etc.) or a
            // refinement (Nat).  If neither, check if it's a variant constructor
            // or a struct constructor / projector.
            Term::Builtin(name) | Term::Global(name) => {
                if self.checker_extern_requires_unsafe(name) {
                    return Err(Diagnostic::new(format!(
                        "call to external function `{}` requires an unsafe context",
                        name
                    )));
                }
                if let Some(sig) = self.lookup_extern(name) {
                    return self.check_domain_match(sig, constraint);
                }
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

    fn checker_extern_requires_unsafe(&self, name: &str) -> bool {
        self.lookup_extern(name).is_some() && self.unsafe_depth == 0
    }

    fn check_pure(
        &self,
        ctx: &Context<'bump>,
        inner: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        if self.unsafe_depth == 0 {
            return Err(Diagnostic::new(
                "`pure` can only appear in an unsafe context",
            ));
        }
        let inferred = self.infer_binding_constraint(ctx, inner)?;
        let effect_constraint = self.evaluator.whnf(inferred)?;
        let Some(inner_constraint) = self.io_inner(effect_constraint) else {
            return Err(Diagnostic::new(format!(
                "`pure` expects an IO constraint, got {}",
                crate::pretty::PrettyPrinter::pretty(effect_constraint)
            )));
        };
        self.check(ctx, inner, effect_constraint)?;
        self.check_domain_match(inner_constraint, constraint)
    }

    pub(crate) fn io_inner(&self, t: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        if let Term::App(head, inner) = t
            && matches!(head, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_IO))
        {
            return Some(inner);
        }
        None
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
            enum_table: Vec::new(),
            struct_table: Vec::new(),
            extern_table: Vec::new(),
            instance_table: Vec::new(),
            unsafe_depth: 0,
            mode: CheckMode::Full,
        }
    }

    fn clone_for_unsafe(&self) -> Self {
        Self {
            arena: self.arena,
            evaluator: WhnfEvaluator::new(self.arena),
            builtins: self.builtins.clone(),
            table: self.table.clone(),
            enum_table: self.enum_table.clone(),
            struct_table: self.struct_table.clone(),
            extern_table: self.extern_table.clone(),
            instance_table: self.instance_table.clone(),
            unsafe_depth: self.unsafe_depth,
            mode: self.mode,
        }
    }

    fn check_by_proof_fast(
        &self,
        ctx: &Context<'bump>,
        subject: Option<&'bump Term<'bump>>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), Diagnostic> {
        let Some(subject) = subject else {
            return Ok(());
        };
        let constraint_nf = self.evaluator.whnf(constraint)?;
        let expanded = match constraint_nf {
            Term::Builtin(name) | Term::Global(name) => lookup_refine(name, &self.table)
                .map(|(parent, predicate)| self.arena.refine(name, parent, predicate)),
            _ => None,
        };
        match expanded.unwrap_or(constraint_nf) {
            Term::Refine(_, parent, _) => self.check(ctx, subject, parent),
            _ => self.check(ctx, subject, constraint),
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
        enum_table: Vec::new(),
        struct_table: Vec::new(),
        extern_table: Vec::new(),
        instance_table: Vec::new(),
        unsafe_depth: 0,
        mode: CheckMode::Full,
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
