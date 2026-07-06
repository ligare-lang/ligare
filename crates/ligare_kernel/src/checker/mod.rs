pub mod builtin;
pub mod context;
mod engine;
pub mod erase;
pub mod infer;
pub mod prove;
pub use engine::check;

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
    pub arena: &'bump TermArena<'bump>,
    pub evaluator: WhnfEvaluator<'bump>,
    pub builtins: BuiltinRegistry,
    pub table: ConstraintTable<'bump>,
    /// Registry of enum definitions: maps enum name → (EnumDef term, param_names)
    pub enum_table: Vec<(Name<'bump>, &'bump Term<'bump>, &'bump [Name<'bump>])>,
    /// Registry of struct definitions: maps struct name → (StructDef term, param_names)
    pub struct_table: Vec<(Name<'bump>, &'bump Term<'bump>, &'bump [Name<'bump>])>,
    /// External C function signatures.
    pub extern_table: Vec<(Name<'bump>, &'bump Term<'bump>)>,
    /// Compile-time implicit instances: name, constraint, value.
    pub instance_table: Vec<(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>)>,
    /// Whether the current check is inside an explicit unsafe expression.
    pub unsafe_depth: usize,
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
                self.lookup_method_on_instance(method, receiver_constraint, name, have, value)
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

    pub fn implicit_inner(t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Implicit(inner) => inner,
            _ => t,
        }
    }

    pub fn is_implicit_constraint(t: &Term<'_>) -> bool {
        matches!(t, Term::Implicit(_))
    }

    pub(crate) fn lookup_extern(&self, name: &str) -> Option<&'bump Term<'bump>> {
        self.extern_table
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, sig)| *sig)
    }

}
