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

    // ── Preamble ──
    out.push_str("const std = @import(\"std\");\n\n");

    // ── Collect defs and output expressions ──
    let mut defs: Vec<(&str, &Term<'_>)> = Vec::new();
    let mut outputs: Vec<&Term<'_>> = Vec::new();

    for top in tops {
        match top {
            TopLevel::TLDef(name, term) => {
                // Skip refinement type definitions (type-level only)
                if matches!(term, Term::Refine(_, _, _)) {
                    continue;
                }
                defs.push((name, term));
            }
            TopLevel::TLCheck(_, _) => {} // compile-time only
            TopLevel::TLShow(term) | TopLevel::TLExpr(term) => outputs.push(term),
        }
    }

    // ── Emit function / constant definitions ──
    for (name, term) in &defs {
        out.push_str(&emit_def(name, term));
        out.push('\n');
    }

    // ── Emit main ──
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

/// Emit a top-level definition as a Zig function or constant.
fn emit_def(name: &str, term: &Term<'_>) -> String {
    // Peel off Annot wrapper
    let inner = match term {
        Term::Annot(t, _) => t,
        _ => term,
    };

    // Count nested Lams to determine arity
    let arity = count_lams(inner);

    if arity == 0 {
        // Simple constant definition
        let val = emit_term(inner, &[], None);
        format!("const {} = {};\n", name, val)
    } else {
        // Function definition
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

/// Count how many nested `Lam` wrappers there are.
fn count_lams(term: &Term<'_>) -> usize {
    match term {
        Term::Lam(body) => 1 + count_lams(body),
        _ => 0,
    }
}

/// Peel off `n` layers of `Lam` and return the body.
fn peel_lams<'bump>(term: &'bump Term<'bump>, n: usize) -> &'bump Term<'bump> {
    let mut t = term;
    for _ in 0..n {
        if let Term::Lam(body) = t {
            t = body;
        }
    }
    t
}

/// Emit a term as a Zig expression string.
///
/// `bound` maps de Bruijn indices (0 = innermost) to Zig variable names.
/// `self_name` is the name of the enclosing function (for `This` recursion).
fn emit_term(term: &Term<'_>, bound: &[String], self_name: Option<&str>) -> String {
    match term {
        // ── Leaf values ──
        Term::LitInt(n) => n.to_string(),
        Term::LitBool(b) => {
            if *b {
                "true".to_string()
            } else {
                "false".to_string()
            }
        }
        Term::Var(i) => bound[*i].clone(),

        // ── Self-reference (recursion) ──
        Term::This => self_name.unwrap_or("__self__").to_string(),

        // ── Top-level name reference ──
        Term::Builtin(name) => (*name).to_string(),

        // ── Type erasure ──
        Term::Annot(inner, _) | Term::ByProof(inner, _) | Term::ProofBlock(inner) => {
            emit_term(inner, bound, self_name)
        }

        // ── If-then-else ──
        Term::IfThenElse(cond, tbranch, fbranch) => {
            let c = emit_term(cond, bound, self_name);
            let t = emit_term(tbranch, bound, self_name);
            let f = emit_term(fbranch, bound, self_name);
            format!("if ({}) {{ {} }} else {{ {} }}", c, t, f)
        }

        // ── Let binding ──
        Term::Let(name, val, body, _) => {
            let v = emit_term(val, bound, self_name);
            let mut extended: Vec<String> = vec![(*name).to_string()];
            extended.extend_from_slice(bound);
            let b = emit_term(body, &extended, self_name);
            format!("{{ const {} = {}; {} }}", name, v, b)
        }

        // ── Lambda (should only appear as inline, not at top-level) ──
        Term::Lam(body) => {
            // Generate a fresh name for the bound variable
            let mut extended: Vec<String> = vec!["_x".to_string()];
            extended.extend_from_slice(bound);
            let b = emit_term(body, &extended, self_name);
            format!(
                "(struct {{ fn call(_x: i64) i64 {{ return {}; }} }}.call)",
                b
            )
        }

        // ── Application ──
        Term::App(_, _) => emit_app(term, bound, self_name),

        // ── Type-level terms (should not appear at runtime) ──
        Term::Pi(_, _, _)
        | Term::Universe(_)
        | Term::AutoProof
        | Term::RefParam
        | Term::Refine(_, _, _)
        | Term::Func { .. }
        | Term::PrimOp(_) => "/* type-level */ @as(i64, 0)".to_string(),
    }
}

/// Emit an application, detecting binary operators and function calls.
fn emit_app(term: &Term<'_>, bound: &[String], self_name: Option<&str>) -> String {
    let Term::App(f, a) = term else {
        unreachable!()
    };

    // Detect binary operator: App(App(PrimOp(op), left), right)
    // `f` is `&Term<'_>`; pattern-match through the reference.
    if let Term::App(prim, left) = f {
        if let Term::PrimOp(op) = prim {
            let left_str = emit_term(left, bound, self_name);
            let right_str = emit_term(a, bound, self_name);
            return emit_binop(*op, &left_str, &right_str);
        }
    }

    // Detect PrimOp + single arg (curried, should not happen but handle)
    if let Term::PrimOp(_) = **f {
        let right_str = emit_term(a, bound, self_name);
        return format!("/* partial-op */ {}", right_str);
    }

    // Function call: collect all arguments in the App chain
    let mut args: Vec<String> = Vec::new();
    let func = collect_call_args(term, bound, self_name, &mut args);
    format!("{}({})", func, args.join(", "))
}

/// Recursively collect arguments from a curried App chain.
/// Returns the function expression string.
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

/// Emit a binary operator.
fn emit_binop(op: PrimOp, left: &str, right: &str) -> String {
    match op {
        PrimOp::Add => format!("({} + {})", left, right),
        PrimOp::Sub => format!("({} - {})", left, right),
        PrimOp::Mul => format!("({} * {})", left, right),
        // Ligare erases proof/prop/theorem terms after compile-time
        // verification — the generated code is pure data with zero
        // runtime overhead from the constraint system.
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

    #[test]
    fn emit_simple_function() {
        let (_bump, arena) = a();
        // def add1 (x : int) : int := x + 1
        // After parsing: Annot(Lam(App(App(+, Var(0)), 1)), int)
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(0)),
            arena.lit_int(1),
        );
        let lam = arena.lam(body);
        let term = arena.annot(lam, arena.builtin(ns(&arena, "int")));
        let tops = vec![TopLevel::TLDef(ns(&arena, "add1"), term)];
        let zig = emit_zig(&tops);
        assert!(zig.contains("fn add1("), "expected fn add1, got:\n{}", zig);
        assert!(
            zig.contains("arg_0 + 1"),
            "expected arg_0 + 1, got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_constant() {
        let (_bump, arena) = a();
        let term = arena.annot(arena.lit_int(42), arena.builtin(ns(&arena, "int")));
        let tops = vec![TopLevel::TLDef(ns(&arena, "answer"), term)];
        let zig = emit_zig(&tops);
        assert!(
            zig.contains("const answer = 42;"),
            "expected const answer, got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_recursive_function() {
        let (_bump, arena) = a();
        // def fib (n : int) : int := if n < 2 then n else fib (n-1) + fib (n-2)
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
        let lam = arena.lam(body);
        let term = arena.annot(lam, arena.builtin(ns(&arena, "int")));
        let tops = vec![TopLevel::TLDef(ns(&arena, "fib"), term)];
        let zig = emit_zig(&tops);
        assert!(
            zig.contains("fn fib(") && zig.contains("fib("),
            "expected recursive fib, got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_show_produces_main() {
        let (_bump, arena) = a();
        let tops = vec![TopLevel::TLShow(arena.lit_int(42))];
        let zig = emit_zig(&tops);
        assert!(
            zig.contains("pub fn main()"),
            "expected main, got:\n{}",
            zig
        );
        assert!(zig.contains("42"), "expected 42, got:\n{}", zig);
    }

    #[test]
    fn emit_multi_arg_function() {
        let (_bump, arena) = a();
        // def add (a : int) (b : int) := a + b
        // After parsing: Lam(Lam(App(App(+, Var(1)), Var(0))))
        let inner = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(1)),
            arena.var(0),
        );
        let lam2 = arena.lam(inner);
        let lam1 = arena.lam(lam2);
        let tops = vec![TopLevel::TLDef(ns(&arena, "add"), lam1)];
        let zig = emit_zig(&tops);
        assert!(
            zig.contains("fn add(arg_0: i64, arg_1: i64)"),
            "expected two params, got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_comparison_operators() {
        let (_bump, arena) = a();
        // Lam(App(App(==, Var(0)), LitInt(0)))
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Eq), arena.var(0)),
            arena.lit_int(0),
        );
        let lam = arena.lam(body);
        let tops = vec![TopLevel::TLDef(ns(&arena, "is_zero"), lam)];
        let zig = emit_zig(&tops);
        assert!(
            zig.contains("arg_0 == 0"),
            "expected comparison, got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_division() {
        let (_bump, arena) = a();
        // Lam(Lam(App(App(/, Var(1)), Var(0))))
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Div), arena.var(1)),
            arena.var(0),
        );
        let lam2 = arena.lam(body);
        let lam1 = arena.lam(lam2);
        let tops = vec![TopLevel::TLDef(ns(&arena, "sdiv"), lam1)];
        let zig = emit_zig(&tops);
        assert!(
            zig.contains("@divTrunc"),
            "expected @divTrunc, got:\n{}",
            zig
        );
        // No zero-check: Ligare erases proof constraints at compile time
        assert!(
            !zig.contains("== 0"),
            "should NOT have zero-check (type system proves it), got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_skips_refinement_def() {
        let (_bump, arena) = a();
        // def nat := int where (x => x >= 0)
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
        // nat should NOT appear as a const/fn in the output
        assert!(
            !zig.contains("nat"),
            "refinement type should be skipped, got:\n{}",
            zig
        );
        assert!(zig.contains("42"), "expected 42 in main, got:\n{}", zig);
    }

    #[test]
    fn emit_let_binding() {
        let (_bump, arena) = a();
        // def answer := let x := 40 in x + 2
        let body = arena.let_(
            ns(&arena, "x"),
            arena.lit_int(40),
            arena.app(
                arena.app(arena.prim_op(PrimOp::Add), arena.var(0)),
                arena.lit_int(2),
            ),
            None,
        );
        let tops = vec![TopLevel::TLDef(ns(&arena, "answer"), body)];
        let zig = emit_zig(&tops);
        assert!(zig.contains("const x = 40"), "expected let, got:\n{}", zig);
        assert!(
            zig.contains("x + 2") || zig.contains("x+2"),
            "expected x + 2, got:\n{}",
            zig
        );
    }

    #[test]
    fn emit_if_then_else_top_level() {
        let (_bump, arena) = a();
        let term = arena.if_then_else(arena.lit_bool(true), arena.lit_int(10), arena.lit_int(20));
        let tops = vec![TopLevel::TLShow(term)];
        let zig = emit_zig(&tops);
        assert!(
            zig.contains("10"),
            "expected 10 in if-branch, got:\n{}",
            zig
        );
        assert!(zig.contains("if (true)"), "expected if, got:\n{}", zig);
    }

    #[test]
    fn emit_boolean_show_handled() {
        let (_bump, arena) = a();
        let tops = vec![TopLevel::TLShow(arena.lit_bool(true))];
        let zig = emit_zig(&tops);
        assert!(zig.contains("true"), "expected true, got:\n{}", zig);
    }
}
