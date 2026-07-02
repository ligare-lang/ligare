use crate::compiler::Compiler;
use crate::core::syntax::{Tactic, Term};

impl<'bump> Compiler<'bump> {
    pub(super) fn replace_type_param_vars(
        &self,
        term: &'bump Term<'bump>,
        type_args: &[&'bump Term<'bump>],
        scope_len: usize,
    ) -> &'bump Term<'bump> {
        let type_param_indices = (0..type_args.len())
            .map(|idx| scope_len - 1 - idx)
            .collect::<Vec<_>>();
        self.replace_type_param_vars_at(term, type_args, &type_param_indices, 0)
    }

    fn replace_type_param_vars_at(
        &self,
        term: &'bump Term<'bump>,
        type_args: &[&'bump Term<'bump>],
        type_param_indices: &[usize],
        depth: usize,
    ) -> &'bump Term<'bump> {
        match term {
            Term::Var(i) if *i >= depth => {
                let outer_idx = *i - depth;
                type_param_indices
                    .iter()
                    .position(|idx| *idx == outer_idx)
                    .and_then(|type_idx| type_args.get(type_idx).copied())
                    .unwrap_or(term)
            }
            Term::App(f, a) => self.arena.app(
                self.replace_type_param_vars_at(f, type_args, type_param_indices, depth),
                self.replace_type_param_vars_at(a, type_args, type_param_indices, depth),
            ),
            Term::Implicit(inner) => self.arena.implicit(self.replace_type_param_vars_at(
                inner,
                type_args,
                type_param_indices,
                depth,
            )),
            Term::Lam(body) => self.arena.lam(self.replace_type_param_vars_at(
                body,
                type_args,
                type_param_indices,
                depth + 1,
            )),
            Term::Pi(name, dom, cod) => self.arena.pi(
                name,
                self.replace_type_param_vars_at(dom, type_args, type_param_indices, depth),
                self.replace_type_param_vars_at(cod, type_args, type_param_indices, depth + 1),
            ),
            Term::Let(name, value, body, constraint) => {
                let constraint = constraint.map(|c| {
                    self.replace_type_param_vars_at(c, type_args, type_param_indices, depth)
                });
                self.arena.let_(
                    name,
                    self.replace_type_param_vars_at(value, type_args, type_param_indices, depth),
                    self.replace_type_param_vars_at(body, type_args, type_param_indices, depth + 1),
                    constraint,
                )
            }
            Term::IfThenElse(cond, then_branch, else_branch) => self.arena.if_then_else(
                self.replace_type_param_vars_at(cond, type_args, type_param_indices, depth),
                self.replace_type_param_vars_at(then_branch, type_args, type_param_indices, depth),
                self.replace_type_param_vars_at(else_branch, type_args, type_param_indices, depth),
            ),
            Term::Refine(name, parent, pred) => self.arena.refine(
                name,
                self.replace_type_param_vars_at(parent, type_args, type_param_indices, depth),
                self.replace_type_param_vars_at(pred, type_args, type_param_indices, depth),
            ),
            Term::Annot(inner, constraint) => self.arena.annot(
                self.replace_type_param_vars_at(inner, type_args, type_param_indices, depth),
                self.replace_type_param_vars_at(constraint, type_args, type_param_indices, depth),
            ),
            Term::ByProof(inner, tactics) => {
                let inner = inner.map(|t| {
                    self.replace_type_param_vars_at(t, type_args, type_param_indices, depth)
                });
                let tactics = tactics
                    .iter()
                    .map(|tactic| match tactic {
                        Tactic::Exact(t) => Tactic::Exact(self.replace_type_param_vars_at(
                            t,
                            type_args,
                            type_param_indices,
                            depth,
                        )),
                        Tactic::Apply(t) => Tactic::Apply(self.replace_type_param_vars_at(
                            t,
                            type_args,
                            type_param_indices,
                            depth,
                        )),
                        Tactic::Intro(_) => *tactic,
                        Tactic::Have(name, t) => Tactic::Have(
                            name,
                            self.replace_type_param_vars_at(
                                t,
                                type_args,
                                type_param_indices,
                                depth,
                            ),
                        ),
                    })
                    .collect::<Vec<_>>();
                self.arena.by_proof(inner, self.arena.alloc_slice(&tactics))
            }
            Term::EnumDef(name, variants) => {
                let variants = variants
                    .iter()
                    .map(|(variant_name, fields)| {
                        let fields = fields
                            .iter()
                            .map(|(field_name, constraint)| {
                                (
                                    *field_name,
                                    self.replace_type_param_vars_at(
                                        constraint,
                                        type_args,
                                        type_param_indices,
                                        depth,
                                    ),
                                )
                            })
                            .collect::<Vec<_>>();
                        (*variant_name, self.arena.alloc_slice(&fields))
                    })
                    .collect::<Vec<_>>();
                self.arena.enum_def(name, self.arena.alloc_slice(&variants))
            }
            Term::Variant(name, idx, payloads) => {
                let payloads = payloads
                    .iter()
                    .map(|payload| {
                        self.replace_type_param_vars_at(
                            payload,
                            type_args,
                            type_param_indices,
                            depth,
                        )
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .variant(name, *idx, self.arena.alloc_slice(&payloads))
            }
            Term::Match(scrutinee, branches) => {
                let branches = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let binds = binds
                            .iter()
                            .map(|(name, constraint)| {
                                (
                                    *name,
                                    self.replace_type_param_vars_at(
                                        constraint,
                                        type_args,
                                        type_param_indices,
                                        depth,
                                    ),
                                )
                            })
                            .collect::<Vec<_>>();
                        (
                            *idx,
                            self.arena.alloc_slice(&binds),
                            self.replace_type_param_vars_at(
                                body,
                                type_args,
                                type_param_indices,
                                depth + binds.len(),
                            ),
                        )
                    })
                    .collect::<Vec<_>>();
                self.arena.match_(
                    self.replace_type_param_vars_at(
                        scrutinee,
                        type_args,
                        type_param_indices,
                        depth,
                    ),
                    self.arena.alloc_slice(&branches),
                )
            }
            Term::StructDef(name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(field_name, constraint)| {
                        (
                            *field_name,
                            self.replace_type_param_vars_at(
                                constraint,
                                type_args,
                                type_param_indices,
                                depth,
                            ),
                        )
                    })
                    .collect::<Vec<_>>();
                self.arena.struct_def(name, self.arena.alloc_slice(&fields))
            }
            Term::StructCons(name, values) => {
                let values = values
                    .iter()
                    .map(|value| {
                        self.replace_type_param_vars_at(value, type_args, type_param_indices, depth)
                    })
                    .collect::<Vec<_>>();
                self.arena
                    .struct_cons(name, self.arena.alloc_slice(&values))
            }
            Term::StructProj(subject, idx) => self.arena.struct_proj(
                self.replace_type_param_vars_at(subject, type_args, type_param_indices, depth),
                *idx,
            ),
            Term::Unsafe(inner) => self.arena.unsafe_(self.replace_type_param_vars_at(
                inner,
                type_args,
                type_param_indices,
                depth,
            )),
            Term::Pure(inner) => self.arena.pure(self.replace_type_param_vars_at(
                inner,
                type_args,
                type_param_indices,
                depth,
            )),
            Term::Named(_) | Term::NamedLam(..) | Term::NamedMatch(..) => {
                panic!("parser-level term reached generic instantiation before desugaring")
            }
            _ => term,
        }
    }
}
