use crate::core::pool::TermArena;
use crate::core::syntax::{Tactic, Term};

pub struct SubstitutionContext<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> SubstitutionContext<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    pub fn subst(
        &self,
        s: &'bump Term<'bump>,
        i: usize,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.subst_cutoff(s, i, 0, t)
    }

    fn subst_cutoff(
        &self,
        s: &'bump Term<'bump>,
        i: usize,
        cutoff: usize,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        if let Term::Var(j) = t
            && *j == i + cutoff
        {
            return self.shift(cutoff as i32, 0, s);
        }
        self.traverse_children(t, cutoff as i32, |t, c| {
            self.subst_cutoff(s, i, c as usize, t)
        })
    }

    pub fn shift(&self, d: i32, cutoff: i32, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Term::Var(j) = t
            && (*j as i32) >= cutoff
        {
            return self.arena.var((*j as i32 + d) as usize);
        }
        self.traverse_children(t, cutoff, |t, c| self.shift(d, c, t))
    }

    fn traverse_children(
        &self,
        t: &'bump Term<'bump>,
        cutoff: i32,
        recurse: impl Fn(&'bump Term<'bump>, i32) -> &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::Lam(body) => self.arena.lam(recurse(body, cutoff + 1)),
            Term::NamedLam(n, body) => self.arena.named_lam(n, recurse(body, cutoff + 1)),
            Term::App(f, a) => self.arena.app(recurse(f, cutoff), recurse(a, cutoff)),
            Term::Implicit(inner) => self.arena.implicit(recurse(inner, cutoff)),
            Term::Pi(n, a, b) => self.arena.pi(n, recurse(a, cutoff), recurse(b, cutoff + 1)),
            Term::Let(n, v, b, mc) => {
                let mc2 = mc.map(|c| recurse(c, cutoff));
                self.arena
                    .let_(n, recurse(v, cutoff), recurse(b, cutoff + 1), mc2)
            }
            Term::IfThenElse(c, th, el) => self.arena.if_then_else(
                recurse(c, cutoff),
                recurse(th, cutoff),
                recurse(el, cutoff),
            ),
            Term::Annot(inner, ct) => self
                .arena
                .annot(recurse(inner, cutoff), recurse(ct, cutoff)),
            Term::ByProof(inner, tactics) => {
                let inner_mapped = inner.map(|t| recurse(t, cutoff));
                let mapped: Vec<Tactic<'bump>> = tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => Tactic::Exact(recurse(t, cutoff)),
                        Tactic::Apply(t) => Tactic::Apply(recurse(t, cutoff)),
                        Tactic::Intro(_) => *tac,
                        Tactic::Have(n, t) => Tactic::Have(n, recurse(t, cutoff)),
                        Tactic::Custom(n, args) => {
                            let args = args
                                .iter()
                                .map(|arg| recurse(arg, cutoff))
                                .collect::<Vec<_>>();
                            Tactic::Custom(n, self.arena.alloc_slice(&args))
                        }
                    })
                    .collect();
                self.arena
                    .by_proof(inner_mapped, self.arena.alloc_slice(&mapped))
            }
            Term::Refine(n, par, p) => {
                self.arena
                    .refine(n, recurse(par, cutoff), recurse(p, cutoff))
            }
            Term::EnumDef(name, variants) => {
                let mapped: Vec<_> = variants
                    .iter()
                    .map(|(vname, fields)| {
                        let mf: Vec<_> = fields
                            .iter()
                            .map(|(fnm, fc)| (*fnm, recurse(fc, cutoff)))
                            .collect();
                        (*vname, self.arena.alloc_slice(&mf))
                    })
                    .collect();
                self.arena.enum_def(name, self.arena.alloc_slice(&mapped))
            }
            Term::Variant(name, idx, payloads) => {
                let mapped: Vec<_> = payloads.iter().map(|p| recurse(p, cutoff)).collect();
                self.arena
                    .variant(name, *idx, self.arena.alloc_slice(&mapped))
            }
            Term::Match(scrut, branches) => {
                let s = recurse(scrut, cutoff);
                let mapped: Vec<_> = branches
                    .iter()
                    .map(|(idx, binds, body)| {
                        let mb: Vec<_> = binds
                            .iter()
                            .map(|(n, c)| (*n, recurse(c, cutoff)))
                            .collect();
                        (
                            *idx,
                            self.arena.alloc_slice(&mb),
                            recurse(body, cutoff + binds.len() as i32),
                        )
                    })
                    .collect();
                self.arena.match_(s, self.arena.alloc_slice(&mapped))
            }
            Term::StructDef(name, fields) => {
                let mf: Vec<_> = fields
                    .iter()
                    .map(|(fnm, fc)| (*fnm, recurse(fc, cutoff)))
                    .collect();
                self.arena.struct_def(name, self.arena.alloc_slice(&mf))
            }
            Term::StructCons(name, field_values) => {
                let mapped: Vec<_> = field_values.iter().map(|v| recurse(v, cutoff)).collect();
                self.arena
                    .struct_cons(name, self.arena.alloc_slice(&mapped))
            }
            Term::NamedStructCons(name, fields) => {
                let mapped: Vec<_> = fields
                    .iter()
                    .map(|(field, value)| (*field, recurse(value, cutoff)))
                    .collect();
                self.arena
                    .named_struct_cons(*name, self.arena.alloc_slice(&mapped))
            }
            Term::StructProj(subject, idx) => {
                self.arena.struct_proj(recurse(subject, cutoff), *idx)
            }
            Term::MethodCall(receiver, method) => {
                self.arena.method_call(recurse(receiver, cutoff), method)
            }
            Term::Unsafe(inner) => self.arena.unsafe_(recurse(inner, cutoff)),
            Term::Pure(inner) => self.arena.pure(recurse(inner, cutoff)),
            Term::Quote(inner) => self.arena.quote(recurse(inner, cutoff)),
            Term::Splice(inner) => self.arena.splice(recurse(inner, cutoff)),
            _ => t,
        }
    }

    pub fn beta(
        &self,
        lam_body: &'bump Term<'bump>,
        arg: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let shifted_arg = self.shift(1, 0, arg);
        let substituted = self.subst(shifted_arg, 0, lam_body);
        self.shift(-1, 0, substituted)
    }

    pub fn instantiate_pi(
        &self,
        arg: &'bump Term<'bump>,
        codomain: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let substituted = self.subst(arg, 0, codomain);
        self.shift(-1, 0, substituted)
    }

    pub fn shift_preserve_refparam(&self, d: i32, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.shift_refparam_cutoff(d, 0, t)
    }

    fn shift_refparam_cutoff(
        &self,
        d: i32,
        cutoff: i32,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::RefParam => t,
            Term::Var(i) => {
                if (*i as i32) >= cutoff {
                    self.arena.var((*i as i32 + d) as usize)
                } else {
                    t
                }
            }
            _ => self.shift(d, cutoff, t),
        }
    }
}
