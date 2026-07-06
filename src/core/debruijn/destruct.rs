use crate::core::pool::TermArena;
use crate::core::syntax::Term;

pub fn build_destruct_projections<'bump>(
    arena: &TermArena<'bump>,
    proj_names: &[&'bump str],
    val: &'bump Term<'bump>,
) -> Vec<&'bump Term<'bump>> {
    proj_names
        .iter()
        .enumerate()
        .map(|(i, name)| {
            let shifted_val = if i == 0 {
                val
            } else {
                shift_term(arena, i as i32, 0, val)
            };
            arena.app(arena.named(name), shifted_val)
        })
        .collect()
}

fn shift_term<'bump>(
    arena: &TermArena<'bump>,
    d: i32,
    cutoff: i32,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    if let Term::Var(j) = t
        && (*j as i32) >= cutoff
    {
        return arena.var((*j as i32 + d) as usize);
    }
    match t {
        Term::Lam(body) => arena.lam(shift_term(arena, d, cutoff + 1, body)),
        Term::NamedLam(n, body) => arena.named_lam(n, shift_term(arena, d, cutoff + 1, body)),
        Term::App(f, a) => arena.app(
            shift_term(arena, d, cutoff, f),
            shift_term(arena, d, cutoff, a),
        ),
        Term::Implicit(inner) => arena.implicit(shift_term(arena, d, cutoff, inner)),
        Term::Pi(n, a, b) => arena.pi(
            n,
            shift_term(arena, d, cutoff, a),
            shift_term(arena, d, cutoff + 1, b),
        ),
        Term::Let(n, v, b, mc) => {
            let mc2 = mc.map(|c| shift_term(arena, d, cutoff, c));
            arena.let_(
                n,
                shift_term(arena, d, cutoff, v),
                shift_term(arena, d, cutoff + 1, b),
                mc2,
            )
        }
        Term::IfThenElse(c, th, el) => arena.if_then_else(
            shift_term(arena, d, cutoff, c),
            shift_term(arena, d, cutoff, th),
            shift_term(arena, d, cutoff, el),
        ),
        Term::Annot(inner, ct) => arena.annot(
            shift_term(arena, d, cutoff, inner),
            shift_term(arena, d, cutoff, ct),
        ),
        Term::NamedStructCons(name, fields) => {
            let fields = fields
                .iter()
                .map(|(field, value)| (*field, shift_term(arena, d, cutoff, value)))
                .collect::<Vec<_>>();
            arena.named_struct_cons(*name, arena.alloc_slice(&fields))
        }
        Term::Unsafe(inner) => arena.unsafe_(shift_term(arena, d, cutoff, inner)),
        Term::Pure(inner) => arena.pure(shift_term(arena, d, cutoff, inner)),
        Term::MethodCall(receiver, method) => {
            arena.method_call(shift_term(arena, d, cutoff, receiver), method)
        }
        Term::Quote(inner) => arena.quote(shift_term(arena, d, cutoff, inner)),
        Term::Splice(inner) => arena.splice(shift_term(arena, d, cutoff, inner)),
        _ => t,
    }
}
