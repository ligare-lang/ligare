use super::*;

impl<'bump> TypeChecker<'bump> {
    pub(crate) fn constraint_equiv(&self, a: &'bump Term<'bump>, b: &'bump Term<'bump>) -> bool {
        let Ok(a_val) = self.evaluator.whnf(Self::implicit_inner(a)) else {
            return false;
        };
        let Ok(b_val) = self.evaluator.whnf(Self::implicit_inner(b)) else {
            return false;
        };
        a_val == b_val
            || Self::pi_equiv(a_val, b_val)
            || self.named_constraint_equiv(a_val, b_val)
            || self.named_app_equiv(a_val, b_val)
    }

    pub(crate) fn named_constraint_equiv(
        &self,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> bool {
        let extract = |t: &'bump Term<'bump>| -> Option<(&str, Vec<&'bump Term<'bump>>)> {
            let mut args = Vec::new();
            let mut current = t;
            while let Term::App(f, a) = current {
                args.push(*a);
                current = f;
            }
            args.reverse();
            match current {
                Term::EnumDef(name, _) | Term::StructDef(name, _) => Some((name, args)),
                Term::Builtin(name) | Term::Global(name)
                    if self.lookup_enum(name).is_some() || self.lookup_struct(name).is_some() =>
                {
                    Some((name, args))
                }
                _ => None,
            }
        };
        match (extract(a), extract(b)) {
            (Some((n1, args1)), Some((n2, args2)))
                if n1 == n2
                    || crate::config::canonical_builtin_name(n1)
                        == crate::config::canonical_builtin_name(n2) =>
            {
                args1.is_empty()
                    || args2.is_empty()
                    || (args1.len() == args2.len()
                        && args1
                            .iter()
                            .zip(args2.iter())
                            .all(|(x, y)| self.constraint_equiv(x, y)))
            }
            _ => false,
        }
    }

    fn named_app_equiv(&self, a: &'bump Term<'bump>, b: &'bump Term<'bump>) -> bool {
        fn collect<'a>(t: &'a Term<'a>, out: &mut Vec<&'a Term<'a>>) -> &'a Term<'a> {
            match t {
                Term::App(f, arg) => {
                    let head = collect(f, out);
                    out.push(arg);
                    head
                }
                _ => t,
            }
        }
        let mut aa = Vec::new();
        let mut bb = Vec::new();
        let ah = collect(a, &mut aa);
        let bh = collect(b, &mut bb);
        matches!((ah, bh), (Term::Builtin(x) | Term::Global(x), Term::Builtin(y) | Term::Global(y)) if crate::config::canonical_builtin_name(x) == crate::config::canonical_builtin_name(y))
            && aa.len() == bb.len()
            && aa
                .iter()
                .zip(bb.iter())
                .all(|(x, y)| self.constraint_equiv(x, y))
    }

    pub(crate) fn is_implicit_meta_constraint(&self, term: &'bump Term<'bump>) -> bool {
        let Ok(inner) = self.evaluator.whnf(Self::implicit_inner(term)) else {
            return false;
        };
        matches!(
            inner,
            Term::Builtin(name) | Term::Global(name)
                if matches!(
                    crate::config::canonical_builtin_name(name),
                    "prop" | "theorem" | "proof" | "data"
                )
        ) || matches!(
            inner,
            Term::Universe(
                Universe::UProp | Universe::UTheorem | Universe::UProof | Universe::UData
            )
        )
    }

    pub(crate) fn effect_inner(t: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        match t {
            Term::App(_, inner) => Some(inner),
            _ => None,
        }
    }

    pub(crate) fn is_effect_data_marker(t: &'bump Term<'bump>) -> bool {
        if let Term::App(head, inner) = t
            && matches!(head, Term::Builtin(name) | Term::Global(name) if is_builtin_name(name, BUILTIN_IO))
        {
            return Self::is_data_like(inner);
        }
        false
    }

    pub(crate) fn pi_equiv(a: &'bump Term<'bump>, b: &'bump Term<'bump>) -> bool {
        match (a, b) {
            (Term::Pi(_, a_dom, a_cod), Term::Pi(_, b_dom, b_cod)) => {
                Self::simple_constraint_name_equiv(a_dom, b_dom)
                    && (Self::simple_constraint_name_equiv(a_cod, b_cod)
                        || Self::pi_equiv(a_cod, b_cod))
            }
            _ => false,
        }
    }

    fn simple_constraint_name_equiv(a: &Term<'_>, b: &Term<'_>) -> bool {
        a == b
            || matches!(
                (a, b),
                (Term::Builtin(x) | Term::Global(x), Term::Builtin(y) | Term::Global(y))
                    if crate::config::canonical_builtin_name(x)
                        == crate::config::canonical_builtin_name(y)
            )
    }

    pub(crate) fn constraint_name<'a>(&self, t: &Term<'a>) -> &'a str {
        match t {
            Term::Builtin(n) | Term::Global(n) => n,
            Term::Refine(n, _, _) => n,
            _ => "?",
        }
    }

    pub(crate) fn is_refinement_of(&self, t1: &'bump Term<'bump>, t2: &'bump Term<'bump>) -> bool {
        if t1 == t2 {
            return true;
        }
        if Self::is_data_like(t2) {
            return true;
        }
        match t1 {
            Term::Refine(_, parent, _) => self.is_refinement_of(parent, t2),
            Term::Builtin(n) | Term::Global(n) => lookup_refine(n, &self.table)
                .map(|(parent, _)| self.is_refinement_of(parent, t2))
                .unwrap_or(false),
            _ => false,
        }
    }

    pub(crate) fn not_term(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        let body = self.arena.if_then_else(
            self.arena.var(0),
            self.arena.lit_bool(false),
            self.arena.lit_bool(true),
        );
        self.arena.app(self.arena.lam(body), t)
    }
}
