//! Zig code generator — translates Ligare to Zig source code.
//!
//! Design decisions:
//! - `int` → `i64`, `bool` → `bool`
//! - Refinement types are erased (checked at compile time by Ligare)
//! - Recursive calls via `This` use the function name
//! - `#check` / `TLCheck` → ignored (compile-time only)
//! - `#show` / `TLExpr` → `stdout.print` in `main`

use crate::core::syntax::{PrimOp, Term};
use crate::front::parser::TopLevel;

/// Emit Zig source code for a sequence of top-level items.
pub fn emit_zig(tops: &[TopLevel<'_>]) -> String {
    let mut out = String::new();

    out.push_str("const std = @import(\"std\");\n\n");

    let mut defs: Vec<(&str, &Term<'_>)> = Vec::new();
    let mut outputs: Vec<&Term<'_>> = Vec::new();

    for top in tops {
        match top {
            TopLevel::TLDef(name, term) => {
                if matches!(term, Term::Refine(_, _, _)) {
                    continue;
                }
                defs.push((name, term));
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
        out.push_str("pub fn main() !void {\n");
        out.push_str("    const stdout = std.io.getStdOut().writer();\n");
        for term in &outputs {
            let expr = emit_term(term, &[], None);
            out.push_str(&format!(
                "    try stdout.print(\"{{d}}\\n\", .{{{}}});\n",
                expr
            ));
        }
        out.push_str("}\n");
    }

    out
}

fn emit_def(name: &str, term: &Term<'_>) -> String {
    if let Term::Func(_fname, params, m_ret, _pre, _post, body) = term {
        return emit_func_def(name, params, *m_ret, body);
    }

    let inner = match term {
        Term::Annot(t, _) => t,
        _ => term,
    };

    let arity = count_lams(inner);

    if arity == 0 {
        let val = emit_term(inner, &[], None);
        format!("const {} = {};\n", name, val)
    } else {
        let params: Vec<String> = (0..arity).map(|i| format!("arg_{}: i64", i)).collect();
        let param_names: Vec<String> = (0..arity)
            .map(|i| format!("arg_{}", arity - 1 - i))
            .collect();
        let body_str = emit_term(peel_lams(inner, arity), &param_names, Some(name));
        format!(
            "fn {}({}) i64 {{\n    return {};\n}}\n",
            name,
            params.join(", "),
            body_str
        )
    }
}

fn emit_func_def(
    name: &str,
    params: &[(&str, Option<&Term<'_>>)],
    _m_ret: Option<&Term<'_>>,
    body: &Term<'_>,
) -> String {
    let arity = params.len();
    if arity == 0 {
        let val = emit_term(body, &[], None);
        return format!("const {} = {};\n", name, val);
    }

    let zig_params: Vec<String> = params
        .iter()
        .map(|(pn, _)| format!("{}: i64", pn))
        .collect();

    let bound: Vec<String> = params
        .iter()
        .rev()
        .map(|(pn, _)| (*pn).to_string())
        .collect();

    let body_str = emit_term(body, &bound, Some(name));
    format!(
        "fn {}({}) i64 {{\n    return {};\n}}\n",
        name,
        zig_params.join(", "),
        body_str
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
                "true".to_string()
            } else {
                "false".to_string()
            }
        }
        Term::Var(i) => bound[*i].clone(),
        Term::This => self_name.unwrap_or("__self__").to_string(),
        Term::Builtin(name) => (*name).to_string(),

        Term::Annot(inner, _) | Term::ByProof(inner, _) | Term::ProofBlock(inner) => {
            emit_term(inner, bound, self_name)
        }

        Term::IfThenElse(cond, tbranch, fbranch) => {
            let c = emit_term(cond, bound, self_name);
            let t = emit_term(tbranch, bound, self_name);
            let f = emit_term(fbranch, bound, self_name);
            format!("if ({}) {{ {} }} else {{ {} }}", c, t, f)
        }

        Term::Let(name, val, body, _) => {
            let v = emit_term(val, bound, self_name);
            let mut extended: Vec<String> = vec![(*name).to_string()];
            extended.extend_from_slice(bound);
            let b = emit_term(body, &extended, self_name);
            format!("{{ const {} = {}; {} }}", name, v, b)
        }

        Term::Lam(body) => {
            let mut extended: Vec<String> = vec!["_x".to_string()];
            extended.extend_from_slice(bound);
            let b = emit_term(body, &extended, self_name);
            format!(
                "(struct {{ fn call(_x: i64) i64 {{ return {}; }} }}.call)",
                b
            )
        }

        Term::App(_, _) => emit_app(term, bound, self_name),

        Term::Pi(_, _, _)
        | Term::Universe(_)
        | Term::AutoProof
        | Term::RefParam
        | Term::Refine(_, _, _)
        | Term::Func { .. }
        | Term::PrimOp(_) => "@as(i64, 0)".to_string(),
    }
}

fn emit_app(term: &Term<'_>, bound: &[String], self_name: Option<&str>) -> String {
    let Term::App(f, a) = term else {
        unreachable!()
    };

    if let Term::App(prim, left) = f {
        if let Term::PrimOp(op) = prim {
            let left_str = emit_term(left, bound, self_name);
            let right_str = emit_term(a, bound, self_name);
            return emit_binop(*op, &left_str, &right_str);
        }
    }

    if let Term::PrimOp(_) = **f {
        let right_str = emit_term(a, bound, self_name);
        return right_str;
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
        PrimOp::Add => format!("({} + {})", left, right),
        PrimOp::Sub => format!("({} - {})", left, right),
        PrimOp::Mul => format!("({} * {})", left, right),
        PrimOp::Div => format!("@divTrunc({}, {})", left, right),
        PrimOp::Mod_ => format!("@rem({}, {})", left, right),
        PrimOp::Eq => format!("({} == {})", left, right),
        PrimOp::Neq => format!("({} != {})", left, right),
        PrimOp::Lt => format!("({} < {})", left, right),
        PrimOp::Gt => format!("({} > {})", left, right),
        PrimOp::Le => format!("({} <= {})", left, right),
        PrimOp::Ge => format!("({} >= {})", left, right),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::pool::TermArena;
    use crate::core::syntax::PrimOp;
    use crate::front::parser::TopLevel;

    fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(bumpalo::Bump::new()));
        (b, TermArena::new(b))
    }

    fn ns<'bump>(arena: &'bump TermArena<'bump>, s: &str) -> &'bump str {
        arena.alloc_str(s)
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
        let (_bump, arena) = a();
        let pt = Some(arena.builtin(ns(&arena, "int")) as &Term<'_>);
        let params: &[(&str, Option<&Term>)] = arena.alloc_slice(&[(ns(&arena, "x"), pt)]);
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(0)),
            arena.lit_int(1),
        );
        let top = def_func(&arena, ns(&arena, "add1"), params, pt, body);
        let zig = emit_zig(&[top]);
        assert!(zig.contains("fn add1("), "got:\n{}", zig);
        assert!(zig.contains("x: i64"), "got:\n{}", zig);
        assert!(
            zig.contains("x + 1") || zig.contains("x+1"),
            "got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_constant() {
        let (_bump, arena) = a();
        let top = def_func(
            &arena,
            ns(&arena, "answer"),
            &[],
            Some(arena.builtin(ns(&arena, "int"))),
            arena.lit_int(42),
        );
        let zig = emit_zig(&[top]);
        assert!(zig.contains("const answer = 42;"), "got:\n{}", zig);
    }

    #[test]
    fn emit_recursive_function() {
        let (_bump, arena) = a();
        let body = arena.if_then_else(
            arena.app(
                arena.app(arena.prim_op(PrimOp::Lt), arena.var(0)),
                arena.lit_int(2),
            ),
            arena.var(0),
            arena.app(
                arena.app(
                    arena.prim_op(PrimOp::Add),
                    arena.app(
                        arena.this_(),
                        arena.app(
                            arena.app(arena.prim_op(PrimOp::Sub), arena.var(0)),
                            arena.lit_int(1),
                        ),
                    ),
                ),
                arena.app(
                    arena.this_(),
                    arena.app(
                        arena.app(arena.prim_op(PrimOp::Sub), arena.var(0)),
                        arena.lit_int(2),
                    ),
                ),
            ),
        );
        let pt = Some(arena.builtin(ns(&arena, "int")) as &Term<'_>);
        let params: &[(&str, Option<&Term>)] = arena.alloc_slice(&[(ns(&arena, "n"), pt)]);
        let top = def_func(&arena, ns(&arena, "fib"), params, pt, body);
        let zig = emit_zig(&[top]);
        assert!(zig.contains("fn fib("), "got:\n{}", zig);
        assert!(zig.contains("n: i64"), "got:\n{}", zig);
        assert!(zig.contains("fib("), "got:\n{}", zig);
    }

    #[test]
    fn emit_show_produces_main() {
        let (_bump, arena) = a();
        let zig = emit_zig(&[TopLevel::TLShow(arena.lit_int(42))]);
        assert!(zig.contains("pub fn main()"), "got:\n{}", zig);
        assert!(zig.contains("42"), "got:\n{}", zig);
    }

    #[test]
    fn emit_multi_arg_function() {
        let (_bump, arena) = a();
        let pt = Some(arena.builtin(ns(&arena, "int")) as &Term<'_>);
        let params: &[(&str, Option<&Term>)] =
            arena.alloc_slice(&[(ns(&arena, "a"), pt), (ns(&arena, "b"), pt)]);
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(1)),
            arena.var(0),
        );
        let top = def_func(&arena, ns(&arena, "add"), params, None, body);
        let zig = emit_zig(&[top]);
        assert!(zig.contains("fn add(a: i64, b: i64)"), "got:\n{}", zig);
    }

    #[test]
    fn emit_comparison_operators() {
        let (_bump, arena) = a();
        let pt = Some(arena.builtin(ns(&arena, "int")) as &Term<'_>);
        let params: &[(&str, Option<&Term>)] = arena.alloc_slice(&[(ns(&arena, "x"), pt)]);
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Eq), arena.var(0)),
            arena.lit_int(0),
        );
        let top = def_func(&arena, ns(&arena, "is_zero"), params, None, body);
        let zig = emit_zig(&[top]);
        assert!(zig.contains("x == 0"), "got:\n{}", zig);
    }

    #[test]
    fn emit_division() {
        let (_bump, arena) = a();
        let pt = Some(arena.builtin(ns(&arena, "int")) as &Term<'_>);
        let params: &[(&str, Option<&Term>)] =
            arena.alloc_slice(&[(ns(&arena, "a"), pt), (ns(&arena, "b"), pt)]);
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Div), arena.var(1)),
            arena.var(0),
        );
        let top = def_func(&arena, ns(&arena, "sdiv"), params, None, body);
        let zig = emit_zig(&[top]);
        assert!(zig.contains("@divTrunc"), "got:\n{}", zig);
        assert!(!zig.contains("== 0"), "got:\n{}", zig);
    }

    #[test]
    fn emit_skips_refinement_def() {
        let (_bump, arena) = a();
        let pred = arena.lam(arena.app(
            arena.app(arena.prim_op(PrimOp::Ge), arena.var(0)),
            arena.lit_int(0),
        ));
        let refine = arena.refine(ns(&arena, "nat"), arena.builtin(ns(&arena, "int")), pred);
        let tops = vec![
            TopLevel::TLDef(ns(&arena, "nat"), refine),
            TopLevel::TLShow(arena.lit_int(42)),
        ];
        let zig = emit_zig(&tops);
        assert!(!zig.contains("nat"), "got:\n{}", zig);
        assert!(zig.contains("42"), "got:\n{}", zig);
    }

    #[test]
    fn emit_let_binding() {
        let (_bump, arena) = a();
        let body = arena.let_(
            ns(&arena, "x"),
            arena.lit_int(40),
            arena.app(
                arena.app(arena.prim_op(PrimOp::Add), arena.var(0)),
                arena.lit_int(2),
            ),
            None,
        );
        let top = def_func(&arena, ns(&arena, "answer"), &[], None, body);
        let zig = emit_zig(&[top]);
        assert!(zig.contains("const x = 40"), "got:\n{}", zig);
        assert!(
            zig.contains("x + 2") || zig.contains("x+2"),
            "got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_if_then_else_top_level() {
        let (_bump, arena) = a();
        let term = arena.if_then_else(arena.lit_bool(true), arena.lit_int(10), arena.lit_int(20));
        let zig = emit_zig(&[TopLevel::TLShow(term)]);
        assert!(zig.contains("10"), "got:\n{}", zig);
        assert!(zig.contains("if (true)"), "got:\n{}", zig);
    }

    #[test]
    fn emit_boolean_show_handled() {
        let (_bump, arena) = a();
        let zig = emit_zig(&[TopLevel::TLShow(arena.lit_bool(true))]);
        assert!(zig.contains("true"), "got:\n{}", zig);
    }
}
