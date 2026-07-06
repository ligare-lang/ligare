use crate::core::debruijn::SubstitutionContext;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Term, Universe};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtxEntry<'bump> {
    pub name: Name<'bump>,
    pub constraint: &'bump Term<'bump>,
    pub theorems: Vec<&'bump Term<'bump>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context<'bump> {
    entries: Vec<CtxEntry<'bump>>,
}

impl<'bump> Context<'bump> {
    pub fn empty() -> Self {
        Self { entries: vec![] }
    }
    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    pub fn iter(&self) -> impl Iterator<Item = &CtxEntry<'bump>> {
        self.entries.iter()
    }
    pub fn lookup(&self, i: usize) -> Option<&'bump Term<'bump>> {
        self.entries.get(i).map(|e| e.constraint)
    }
    pub fn extend(&self, name: Name<'bump>, constraint: &'bump Term<'bump>) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(
            0,
            CtxEntry {
                name,
                constraint,
                theorems: vec![],
            },
        );
        Self { entries }
    }
    pub fn extend_term(&self, constraint: &'bump Term<'bump>) -> Self {
        self.extend("_", constraint)
    }
    pub fn add_theorem(&self, name: &str, thm: &'bump Term<'bump>) -> Self {
        let entries: Vec<CtxEntry<'bump>> = self
            .entries
            .iter()
            .map(|e| {
                if e.name == name {
                    let mut thms = e.theorems.clone();
                    thms.insert(0, thm);
                    CtxEntry {
                        name: e.name,
                        constraint: e.constraint,
                        theorems: thms,
                    }
                } else {
                    e.clone()
                }
            })
            .collect();
        Self { entries }
    }
}

// ── Convenience free functions (backward compatible) ──

pub fn empty_ctx<'bump>() -> Context<'bump> {
    Context::empty()
}
pub fn extend_ctx<'bump>(
    name: Name<'bump>,
    constraint: &'bump Term<'bump>,
    ctx: &Context<'bump>,
) -> Context<'bump> {
    ctx.extend(name, constraint)
}
pub fn extend_ctx_term<'bump>(
    constraint: &'bump Term<'bump>,
    ctx: &Context<'bump>,
) -> Context<'bump> {
    ctx.extend_term(constraint)
}
pub fn add_theorem<'bump>(
    name: &str,
    thm: &'bump Term<'bump>,
    ctx: &Context<'bump>,
) -> Context<'bump> {
    ctx.add_theorem(name, thm)
}

// ── Constraint Table ──

pub type ConstraintTable<'bump> = Vec<(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>)>;

pub fn empty_table<'bump>() -> ConstraintTable<'bump> {
    vec![]
}

pub fn add_refine<'bump>(
    name: Name<'bump>,
    parent: &'bump Term<'bump>,
    predicate: &'bump Term<'bump>,
    table: &ConstraintTable<'bump>,
) -> ConstraintTable<'bump> {
    let mut t = table.clone();
    t.insert(0, (name, parent, predicate));
    t
}

pub fn lookup_refine<'bump>(
    name: &str,
    table: &ConstraintTable<'bump>,
) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
    table
        .iter()
        .find(|(n, _, _)| *n == name)
        .map(|(_, p, pred)| (*p, *pred))
}

pub fn expand_constraint<'bump>(
    arena: &'bump TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    constraint: &'bump Term<'bump>,
) -> Option<&'bump Term<'bump>> {
    let sub = SubstitutionContext::new(arena);
    let Term::App(builtin, arg) = constraint else {
        return None;
    };
    let (Term::Builtin(name) | Term::Global(name)) = *builtin else {
        return None;
    };
    let (parent, body) = lookup_refine(name, table)?;
    if !matches!(parent, Term::Universe(Universe::UData)) {
        return None;
    }
    let body_shifted = sub.shift_preserve_refparam(1, body);
    let instantiated = sub.subst(arg, 0, body_shifted);
    Some(sub.shift_preserve_refparam(-1, instantiated))
}

pub fn shift_param<'bump>(
    arena: &'bump TermArena<'bump>,
    d: i32,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    SubstitutionContext::new(arena).shift_preserve_refparam(d, t)
}
