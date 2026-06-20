use crate::core::syntax::{PrimOp, Term};
use crate::front::parser::TopLevel;

pub fn emit_zig(tops: &[TopLevel<'_>]) -> String {
    let mut out = String::from("const std = @import(\"std\");\n\n");
    let mut defs: Vec<(&str, &Term<'_>)> = Vec::new();
    let mut outputs: Vec<&Term<'_>> = Vec::new();

    for top in tops {
        match top {
            TopLevel::TLDef(name, term) => {
                if !matches!(term, Term::Refine(_, _, _)) {
                    defs.push((name, term));
                }
            }
            TopLevel::TLCheck(_, _) => {}
            TopLevel::TLShow(term) | TopLevel::TLExpr(term) => outputs.push(term),
        }
    }

    for (name, term) in &defs {
        out.push_str(&emit_def(name, term));
        out.push('\n');
    }

    if !outputs.is_empty() {
        out.push_str("pub fn main() !void {\n    const stdout = std.io.getStdOut().writer();\n");
        for term in &outputs {
            out.push_str(&format!(
                "    try stdout.print(\"{{d}}\\n\", .{{{}}});\n",
                emit_term(term, &[], None)
            ));
        }
        out.push_str("}\n");
    }
    out
}

fn emit_def(name: &str, term: &Term<'_>) -> String {
    let (body, params, self_name) = if let Term::Func(_, params, _, _, _, body) = term {
        (
            *body,
            params
                .iter()
                .map(|(n, _)| (*n).to_string())
                .collect::<Vec<_>>(),
            Some(name),
        )
    } else {
        let inner = match term {
            Term::Annot(t, _) => t,
            _ => term,
        };
        let arity = count_lams(inner);
        if arity == 0 {
            return format!("const {} = {};\n", name, emit_term(inner, &[], None));
        }
        let pns: Vec<String> = (0..arity).rev().map(|i| format!("arg_{}", i)).collect();
        (peel_lams(inner, arity), pns, Some(name))
    };
    if params.is_empty() {
        return format!("const {} = {};\n", name, emit_term(body, &[], None));
    }
    let zps: Vec<String> = params.iter().map(|p| format!("{p}: i64")).collect();
    let bd: Vec<String> = params.iter().rev().cloned().collect();
    format!(
        "fn {}({}) i64 {{\n    return {};\n}}\n",
        name,
        zps.join(", "),
        emit_term(body, &bd, self_name)
    )
}

fn count_lams(term: &Term<'_>) -> usize {
    match term {
        Term::Lam(body) => 1 + count_lams(body),
        _ => 0,
    }
}

fn peel_lams<'bump>(term: &'bump Term<'bump>, n: usize) -> &'bump Term<'bump> {
    let mut t = term;
    for _ in 0..n {
        if let Term::Lam(body) = t {
            t = body;
        }
    }
    t
}

fn emit_term(term: &Term<'_>, bound: &[String], self_name: Option<&str>) -> String {
    match term {
        Term::LitInt(n) => n.to_string(),
        Term::LitBool(b) => {
            if *b {
                "true".into()
            } else {
                "false".into()
            }
        }
        Term::Var(i) => bound[*i].clone(),
        Term::This => self_name.unwrap_or("__self__").to_string(),
        Term::Builtin(name) => (*name).to_string(),
        Term::Annot(inner, _) | Term::ByProof(inner, _) | Term::ProofBlock(inner) => {
            emit_term(inner, bound, self_name)
        }
        Term::IfThenElse(c, t, f) => format!(
            "if ({}) {{ {} }} else {{ {} }}",
            emit_term(c, bound, self_name),
            emit_term(t, bound, self_name),
            emit_term(f, bound, self_name)
        ),
        Term::Let(name, val, body, _) => {
            let v = emit_term(val, bound, self_name);
            let mut ext: Vec<String> = vec![(*name).to_string()];
            ext.extend_from_slice(bound);
            format!(
                "{{ const {} = {}; {} }}",
                name,
                v,
                emit_term(body, &ext, self_name)
            )
        }
        Term::Lam(body) => {
            let mut ext: Vec<String> = vec!["_x".into()];
            ext.extend_from_slice(bound);
            format!(
                "(struct {{ fn call(_x: i64) i64 {{ return {}; }} }}.call)",
                emit_term(body, &ext, self_name)
            )
        }
        Term::App(_, _) => emit_app(term, bound, self_name),
        _ => "@as(i64, 0)".into(),
    }
}

fn emit_app(term: &Term<'_>, bound: &[String], self_name: Option<&str>) -> String {
    let Term::App(f, a) = term else {
        unreachable!()
    };
    if let Term::App(prim, left) = f {
        if let Term::PrimOp(op) = *prim {
            return emit_binop(
                *op,
                &emit_term(left, bound, self_name),
                &emit_term(a, bound, self_name),
            );
        }
    }
    if matches!(**f, Term::PrimOp(_)) {
        return emit_term(a, bound, self_name);
    }
    let mut args: Vec<String> = Vec::new();
    let func = collect_call_args(term, bound, self_name, &mut args);
    format!("{}({})", func, args.join(", "))
}

fn collect_call_args(
    term: &Term<'_>,
    bound: &[String],
    self_name: Option<&str>,
    args: &mut Vec<String>,
) -> String {
    match term {
        Term::App(f, a) => {
            let func = collect_call_args(f, bound, self_name, args);
            args.push(emit_term(a, bound, self_name));
            func
        }
        _ => emit_term(term, bound, self_name),
    }
}

fn emit_binop(op: PrimOp, left: &str, right: &str) -> String {
    match op {
        PrimOp::Add => format!("({left} + {right})"),
        PrimOp::Sub => format!("({left} - {right})"),
        PrimOp::Mul => format!("({left} * {right})"),
        PrimOp::Div => format!("@divTrunc({left}, {right})"),
        PrimOp::Mod_ => format!("@rem({left}, {right})"),
        PrimOp::Eq => format!("({left} == {right})"),
        PrimOp::Neq => format!("({left} != {right})"),
        PrimOp::Lt => format!("({left} < {right})"),
        PrimOp::Gt => format!("({left} > {right})"),
        PrimOp::Le => format!("({left} <= {right})"),
        PrimOp::Ge => format!("({left} >= {right})"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::pool::TermArena;
    use crate::core::syntax::PrimOp;
    use crate::front::parser::TopLevel;

    fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
        (
            Box::leak(Box::new(bumpalo::Bump::new())),
            TermArena::new(Box::leak(Box::new(bumpalo::Bump::new()))),
        )
    }

    fn ns<'bump>(arena: &'bump TermArena<'bump>, s: &str) -> &'bump str {
        arena.alloc_str(s)
    }

    fn int_ty<'bump>(arena: &'bump TermArena<'bump>) -> Option<&'bump Term<'bump>> {
        Some(arena.builtin(ns(arena, "int")) as &Term<'_>)
    }

    fn param<'bump>(
        arena: &'bump TermArena<'bump>,
        n: &str,
    ) -> (&'bump str, Option<&'bump Term<'bump>>) {
        (ns(arena, n), int_ty(arena))
    }

    fn def_func<'bump>(
        arena: &'bump TermArena<'bump>,
        name: &'bump str,
        params: &'bump [(&'bump str, Option<&'bump Term<'bump>>)],
        ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> TopLevel<'bump> {
        TopLevel::TLDef(name, arena.func(name, params, ret, &[], &[], body))
    }

    #[test]
    fn emit_simple_function() {
        let (_b, arena) = a();
        let p: &[(&str, Option<&Term>)] = arena.alloc_slice(&[param(&arena, "x")]);
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(0)),
            arena.lit_int(1),
        );
        let zig = emit_zig(&[def_func(
            &arena,
            ns(&arena, "add1"),
            p,
            int_ty(&arena),
            body,
        )]);
        assert!(
            zig.contains("fn add1(") && zig.contains("x: i64"),
            "got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_constant() {
        let (_b, arena) = a();
        let zig = emit_zig(&[def_func(
            &arena,
            ns(&arena, "answer"),
            &[],
            int_ty(&arena),
            arena.lit_int(42),
        )]);
        assert!(zig.contains("const answer = 42;"), "got:\n{}", zig);
    }

    #[test]
    fn emit_recursive_function() {
        let (_b, arena) = a();
        let sub1 = arena.app(
            arena.app(arena.prim_op(PrimOp::Sub), arena.var(0)),
            arena.lit_int(1),
        );
        let sub2 = arena.app(
            arena.app(arena.prim_op(PrimOp::Sub), arena.var(0)),
            arena.lit_int(2),
        );
        let body = arena.if_then_else(
            arena.app(
                arena.app(arena.prim_op(PrimOp::Lt), arena.var(0)),
                arena.lit_int(2),
            ),
            arena.var(0),
            arena.app(
                arena.app(arena.prim_op(PrimOp::Add), arena.app(arena.this_(), sub1)),
                arena.app(arena.this_(), sub2),
            ),
        );
        let p: &[(&str, Option<&Term>)] = arena.alloc_slice(&[param(&arena, "n")]);
        let zig = emit_zig(&[def_func(&arena, ns(&arena, "fib"), p, int_ty(&arena), body)]);
        assert!(
            zig.contains("fn fib(") && zig.contains("fib("),
            "got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_show_produces_main() {
        let (_b, arena) = a();
        assert!(emit_zig(&[TopLevel::TLShow(arena.lit_int(42))]).contains("pub fn main()"));
    }

    #[test]
    fn emit_multi_arg_function() {
        let (_b, arena) = a();
        let p: &[(&str, Option<&Term>)] =
            arena.alloc_slice(&[param(&arena, "a"), param(&arena, "b")]);
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(1)),
            arena.var(0),
        );
        let zig = emit_zig(&[def_func(&arena, ns(&arena, "add"), p, None, body)]);
        assert!(zig.contains("fn add(a: i64, b: i64)"), "got:\n{}", zig);
    }

    #[test]
    fn emit_comparison_operators() {
        let (_b, arena) = a();
        let p: &[(&str, Option<&Term>)] = arena.alloc_slice(&[param(&arena, "x")]);
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Eq), arena.var(0)),
            arena.lit_int(0),
        );
        assert!(
            emit_zig(&[def_func(&arena, ns(&arena, "is_zero"), p, None, body)]).contains("x == 0")
        );
    }

    #[test]
    fn emit_division() {
        let (_b, arena) = a();
        let p: &[(&str, Option<&Term>)] =
            arena.alloc_slice(&[param(&arena, "a"), param(&arena, "b")]);
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Div), arena.var(1)),
            arena.var(0),
        );
        assert!(
            emit_zig(&[def_func(&arena, ns(&arena, "sdiv"), p, None, body)]).contains("@divTrunc")
        );
    }

    #[test]
    fn emit_skips_refinement_def() {
        let (_b, arena) = a();
        let pred = arena.lam(arena.app(
            arena.app(arena.prim_op(PrimOp::Ge), arena.var(0)),
            arena.lit_int(0),
        ));
        let refine = arena.refine(ns(&arena, "nat"), arena.builtin(ns(&arena, "int")), pred);
        let zig = emit_zig(&[
            TopLevel::TLDef(ns(&arena, "nat"), refine),
            TopLevel::TLShow(arena.lit_int(42)),
        ]);
        assert!(!zig.contains("nat") && zig.contains("42"), "got:\n{}", zig);
    }

    #[test]
    fn emit_let_and_if() {
        let (_b, arena) = a();
        let body = arena.let_(
            ns(&arena, "x"),
            arena.lit_int(40),
            arena.app(
                arena.app(arena.prim_op(PrimOp::Add), arena.var(0)),
                arena.lit_int(2),
            ),
            None,
        );
        let zig = emit_zig(&[def_func(&arena, ns(&arena, "answer"), &[], None, body)]);
        assert!(zig.contains("const x = 40"), "got:\n{}", zig);
        let term = arena.if_then_else(arena.lit_bool(true), arena.lit_int(10), arena.lit_int(20));
        assert!(emit_zig(&[TopLevel::TLShow(term)]).contains("if (true)"));
        assert!(emit_zig(&[TopLevel::TLShow(arena.lit_bool(true))]).contains("true"));
    }
}
