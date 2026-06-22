use crate::config::BUILTIN_DATA;
use crate::core::pool::TermArena;
use crate::core::syntax::Term;

pub struct Desugarer<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> Desugarer<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }
    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    pub fn desugar(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Func(_fname, params, m_ret, body) => self.desugar_func(params, m_ret, body),
            // All other terms (LitInt, LitBool, LitStr, Var, Pi, etc.) pass through unchanged
            _ => t,
        }
    }

    fn desugar_func(
        &self,
        params: &'bump [(crate::core::syntax::Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: &Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let func_body = params.iter().fold(body, |b, _| self.arena.lam(b));
        let default = self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA));
        let func_type = params
            .iter()
            .rfold(m_ret.unwrap_or(default), |b, (pn, mc)| {
                self.arena.pi(pn, mc.unwrap_or(default), b)
            });
        self.arena.annot(func_body, func_type)
    }
}

pub fn desugar<'bump>(arena: &'bump TermArena<'bump>, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
    Desugarer::new(arena).desugar(t)
}
