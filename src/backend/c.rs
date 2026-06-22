//! C code generation backend.
//!
//! Generates straightforward C from erased `Term` trees.  C type
//! inference happens directly during emission via a `var_types` stack
//! that mirrors De Bruijn binding structure.

use crate::backend::ir::{CType, FunSig};
use crate::core::syntax::{PrimOp, Term};
use crate::front::parser::TopLevel;

/// Emit a complete C source file from a list of top-level items.
pub fn emit_c(tops: &[TopLevel<'_>], fun_sigs: &[(&str, FunSig)]) -> String {
    let mut out = String::from("#include <stdio.h>\n#include <stdint.h>\n\n");
    let mut defs: Vec<(&str, &Term<'_>)> = Vec::new();
    let mut outputs: Vec<&Term<'_>> = Vec::new();

    for top in tops {
        match top {
            TopLevel::TLDef(name, term) => {
                defs.push((name, term));
            }
            TopLevel::TLShow(term) | TopLevel::TLExpr(term) => outputs.push(term),
            _ => {}
        }
    }

    for (name, term) in &defs {
        out.push_str(&emit_def(name, term, fun_sigs));
        out.push('\n');
    }

    if !outputs.is_empty() {
        out.push_str("int main(void) {\n");
        for term in &outputs {
            let (expr, ctype) = emit_expr(term, &[], &mut Vec::new(), None, fun_sigs);
            match ctype {
                CType::Str => {
                    out.push_str(&format!("    printf(\"%s\\n\", {});\n", expr));
                }
                CType::Int64 => {
                    out.push_str(&format!("    printf(\"%ld\\n\", (int64_t)({}));\n", expr));
                }
            }
        }
        out.push_str("    return 0;\n}\n");
    }
    out
}

/// Emit a top-level definition as a C function or constant.
fn emit_def(name: &str, term: &Term<'_>, fun_sigs: &[(&str, FunSig)]) -> String {
    match term {
        Term::Func(_, params, _m_ret, body) => {
            let pns: Vec<String> = params.iter().map(|(n, _)| n.to_string()).collect();
            let param_types: Vec<CType> = fun_sigs
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, sig)| sig.param_types.clone())
                .unwrap_or_else(|| vec![CType::Int64; params.len()]);
            emit_fun(name, &pns, &param_types, body, fun_sigs)
        }
        _ => {
            let arity = count_lams(term);
            if arity == 0 {
                let (code, ctype) = emit_expr(term, &[], &mut Vec::new(), None, fun_sigs);
                format!("const {} {} = {};\n", ctype.c_name(), name, code)
            } else {
                let pns: Vec<String> = (0..arity).map(|i| format!("arg_{}", i)).collect();
                let body = peel_lams(term, arity);
                let param_types = vec![CType::Int64; arity];
                emit_fun(name, &pns, &param_types, body, fun_sigs)
            }
        }
    }
}

/// Emit a C function with named parameters and a Term body.
///
/// `params` are the parameter names; `param_types` are the corresponding C types.
/// De Bruijn index 0 = rightmost (last) parameter.
fn emit_fun(
    name: &str,
    params: &[String],
    param_types: &[CType],
    body: &Term<'_>,
    fun_sigs: &[(&str, FunSig)],
) -> String {
    let cps: Vec<String> = params
        .iter()
        .zip(param_types.iter())
        .map(|(p, ty)| format!("{} {p}", ty.c_name()))
        .collect();
    let bd: Vec<String> = params.iter().rev().cloned().collect();
    let mut var_types: Vec<CType> = param_types.iter().rev().copied().collect();
    let (body_code, ret_ty) = emit_expr(body, &bd, &mut var_types, Some(name), fun_sigs);
    format!(
        "{} {}({}) {{\n    return {};\n}}\n",
        ret_ty.c_name(),
        name,
        cps.join(", "),
        body_code
    )
}

fn count_lams(term: &Term<'_>) -> usize {
    match term {
        Term::Lam(body) => 1 + count_lams(body),
        _ => 0,
    }
}

fn peel_lams<'a>(term: &'a Term<'a>, n: usize) -> &'a Term<'a> {
    let mut t = term;
    for _ in 0..n {
        if let Term::Lam(body) = t {
            t = body;
        }
    }
    t
}

/// Emit a Term as a C expression, returning the emitted code and its C type.
///
/// `bound` holds the C variable names in De Bruijn order (index 0 = most
/// recently bound).  `var_types` holds the C types in the same De Bruijn
/// order — the two stacks are kept in sync by push/pop at binder sites.
/// `self_name` is `Some(name)` inside a recursive function body (so `This`
/// can emit the function name).
fn emit_expr(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
) -> (String, CType) {
    match term {
        Term::LitInt(n) => (n.to_string(), CType::Int64),
        Term::LitBool(b) => (if *b { "1" } else { "0" }.into(), CType::Int64),
        Term::LitStr(s) => (format!("\"{}\"", s), CType::Str),

        Term::Var(i) => {
            let ty = var_types.get(*i).copied().unwrap_or(CType::Int64);
            (bound[*i].clone(), ty)
        }

        Term::Let(name, val, body, _) => {
            let (v, val_ty) = emit_expr(val, bound, var_types, self_name, fun_sigs);
            var_types.insert(0, val_ty);
            let mut ext: Vec<String> = vec![(*name).to_string()];
            ext.extend_from_slice(bound);
            let (b, body_ty) = emit_expr(body, &ext, var_types, self_name, fun_sigs);
            var_types.remove(0);
            (
                format!("({{ {} {} = {}; {}; }})", val_ty.c_name(), name, v, b),
                body_ty,
            )
        }

        Term::Lam(body) => {
            var_types.insert(0, CType::Int64);
            let (b, ret_ty) = emit_expr(body, bound, var_types, self_name, fun_sigs);
            var_types.remove(0);
            // Lambda wrapping is done by emit_fun via emit_def.
            // We return the body code + return type for inference.
            (b, ret_ty)
        }

        Term::Func(fname, params, _m_ret, body) => {
            for _ in 0..params.len() {
                var_types.insert(0, CType::Int64);
            }
            let (b, ret_ty) = emit_expr(body, bound, var_types, Some(fname), fun_sigs);
            for _ in 0..params.len() {
                var_types.remove(0);
            }
            // Func wrapping is done by emit_fun via emit_def.
            (b, ret_ty)
        }

        Term::IfThenElse(c, t, f) => {
            let (cc, _) = emit_expr(c, bound, var_types, self_name, fun_sigs);
            let (ct, t_ty) = emit_expr(t, bound, var_types, self_name, fun_sigs);
            let (cf, _) = emit_expr(f, bound, var_types, self_name, fun_sigs);
            (format!("({}) ? ({}) : ({})", cc, ct, cf), t_ty)
        }

        // Function calls: look up the called function's return type.
        Term::App(_, _) => emit_app(term, bound, var_types, self_name, fun_sigs),

        Term::Annot(inner, _) => emit_expr(inner, bound, var_types, self_name, fun_sigs),
        Term::This => (self_name.unwrap_or("__self__").into(), CType::Int64),
        Term::Builtin(name) => {
            let ty = fun_sigs
                .iter()
                .find(|(n, _)| *n == *name)
                .and_then(|(_, sig)| sig.ret_type)
                .unwrap_or(CType::Int64);
            ((*name).to_string(), ty)
        }
        _ => ("0".into(), CType::Int64),
    }
}

fn emit_app(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
) -> (String, CType) {
    let Term::App(f, a) = term else {
        unreachable!()
    };
    // Binary operators: (prim left) right  →  PrimOp applied to two args.
    if let Term::App(prim, left) = *f
        && let Term::PrimOp(op) = *prim
    {
        let (ls, _) = emit_expr(left, bound, var_types, self_name, fun_sigs);
        let (rs, _) = emit_expr(a, bound, var_types, self_name, fun_sigs);
        return (emit_binop(*op, &ls, &rs), CType::Int64);
    }
    // Unary / partial application: just emit the argument.
    if matches!(*f, Term::PrimOp(_)) {
        let (as_, ty) = emit_expr(a, bound, var_types, self_name, fun_sigs);
        return (as_, ty);
    }
    // Function call.
    let mut args: Vec<String> = Vec::new();
    let func = collect_call_args(term, bound, var_types, self_name, fun_sigs, &mut args);
    let ret_ty = fun_sigs
        .iter()
        .find(|(n, _)| *n == func)
        .and_then(|(_, sig)| sig.ret_type)
        .unwrap_or(CType::Int64);
    (format!("{}({})", func, args.join(", ")), ret_ty)
}

fn collect_call_args(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
    args: &mut Vec<String>,
) -> String {
    match term {
        Term::App(f, a) => {
            let func = collect_call_args(f, bound, var_types, self_name, fun_sigs, args);
            let (as_, _) = emit_expr(a, bound, var_types, self_name, fun_sigs);
            args.push(as_);
            func
        }
        _ => {
            let (s, _) = emit_expr(term, bound, var_types, self_name, fun_sigs);
            s
        }
    }
}

fn emit_binop(op: PrimOp, left: &str, right: &str) -> String {
    match op {
        PrimOp::Add => format!("({left} + {right})"),
        PrimOp::Sub => format!("({left} - {right})"),
        PrimOp::Mul => format!("({left} * {right})"),
        PrimOp::Div => format!("({left} / {right})"),
        PrimOp::Mod_ => format!("({left} % {right})"),
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
    use crate::backend::ir::FunSig;
    use crate::core::pool::TermArena;
    use crate::core::syntax::PrimOp;
    use bumpalo::Bump;

    fn setup() -> (&'static Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        (b, TermArena::new(b))
    }

    fn sig(name: &str, param_types: Vec<CType>, ret_type: Option<CType>) -> (&str, FunSig) {
        // Leak the name string so it lives as long as the test.
        let leaked: &'static str = Box::leak(name.to_string().into_boxed_str());
        (
            leaked,
            FunSig {
                param_types,
                ret_type,
            },
        )
    }

    // ── Literals ──

    #[test]
    fn int_literal_uses_ld() {
        let (_b, arena) = setup();
        let c = emit_c(&[TopLevel::TLShow(arena.lit_int(42))], &[]);
        assert!(c.contains("42"));
        assert!(c.contains("%ld"));
    }

    #[test]
    fn str_literal_uses_s() {
        let (_b, arena) = setup();
        let c = emit_c(
            &[TopLevel::TLShow(arena.lit_str(arena.alloc_str("hi")))],
            &[],
        );
        assert!(c.contains("\"hi\""));
        assert!(c.contains("%s"));
    }

    #[test]
    fn bool_literal_emits_0_or_1() {
        let (_b, arena) = setup();
        let c = emit_c(&[TopLevel::TLShow(arena.lit_bool(true))], &[]);
        assert!(c.contains("(int64_t)(1)"));
    }

    // ── Constants ──

    #[test]
    fn int_const_def() {
        let (_b, arena) = setup();
        let c = emit_c(
            &[TopLevel::TLDef(arena.alloc_str("x"), arena.lit_int(5))],
            &[],
        );
        assert!(c.contains("const int64_t x = 5;"));
    }

    #[test]
    fn str_const_def() {
        let (_b, arena) = setup();
        let c = emit_c(
            &[TopLevel::TLDef(
                arena.alloc_str("g"),
                arena.lit_str(arena.alloc_str("hi")),
            )],
            &[],
        );
        assert!(c.contains("const char* g"));
        assert!(c.contains("\"hi\""));
    }

    // ── Functions (no FunSig, lam-tree) ──

    #[test]
    fn lam_function_defaults_to_int64_params_and_return() {
        let (_b, arena) = setup();
        // \x. \y. x + y
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(1)),
            arena.var(0),
        );
        let lam = arena.lam(arena.lam(body));
        let c = emit_c(&[TopLevel::TLDef(arena.alloc_str("add"), lam)], &[]);
        assert!(c.contains("int64_t add(int64_t arg_0, int64_t arg_1)"));
    }

    #[test]
    fn lam_returning_str_infers_str_return_type() {
        let (_b, arena) = setup();
        let lam = arena.lam(arena.lit_str(arena.alloc_str("hi")));
        let c = emit_c(&[TopLevel::TLDef(arena.alloc_str("greet"), lam)], &[]);
        assert!(c.contains("const char* greet(int64_t arg_0)"));
        assert!(c.contains("\"hi\""));
    }

    // ── Functions WITH FunSig ──

    #[test]
    fn func_with_str_param_uses_const_char_ptr() {
        let (_b, arena) = setup();
        let func = arena.func(
            arena.alloc_str("echo"),
            arena.alloc_slice(&[(
                arena.alloc_str("s"),
                Some(arena.builtin(arena.alloc_str("str"))),
            )]),
            Some(arena.builtin(arena.alloc_str("str"))),
            arena.var(0),
        );
        let sigs = &[sig("echo", vec![CType::Str], Some(CType::Str))];
        let c = emit_c(&[TopLevel::TLDef(arena.alloc_str("echo"), func)], sigs);
        assert!(c.contains("const char* echo(const char* s)"));
    }

    #[test]
    fn func_with_mixed_params() {
        let (_b, arena) = setup();
        let func = arena.func(
            arena.alloc_str("f"),
            arena.alloc_slice(&[
                (
                    arena.alloc_str("a"),
                    Some(arena.builtin(arena.alloc_str("int"))),
                ),
                (
                    arena.alloc_str("b"),
                    Some(arena.builtin(arena.alloc_str("str"))),
                ),
            ]),
            Some(arena.builtin(arena.alloc_str("int"))),
            arena.var(1), // return first param (int)
        );
        let sigs = &[sig("f", vec![CType::Int64, CType::Str], Some(CType::Int64))];
        let c = emit_c(&[TopLevel::TLDef(arena.alloc_str("f"), func)], sigs);
        assert!(c.contains("int64_t f(int64_t a, const char* b)"));
    }

    // ── Function calls ──

    #[test]
    fn call_to_function_uses_fun_sig_return_type() {
        let (_b, arena) = setup();
        let fn_name = arena.alloc_str("greet");
        // def greet : str := "hi"
        let def = TopLevel::TLDef(fn_name, arena.lit_str(arena.alloc_str("hi")));
        // FunSig tells the backend that greet returns a string
        let sig = FunSig {
            param_types: vec![],
            ret_type: Some(CType::Str),
        };
        // #show greet  →  should use %s because greet returns string
        let show = TopLevel::TLShow(arena.builtin(fn_name));
        let tops = &[def, show];
        let c = emit_c(tops, &[(fn_name, sig)]);
        assert!(c.contains("%s"));
        assert!(c.contains("const char* greet"));
    }

    #[test]
    fn emit_undefined_func_call_still_emits() {
        // Even if "s" is undefined at the Term level (constraint checker
        // catches that), the C backend should still emit syntactically
        // valid C for the call.
        let (_b, arena) = setup();
        let n = arena.alloc_str("s");
        let call = arena.app(arena.builtin(n), arena.lit_str(arena.alloc_str("hi")));
        let tops = &[TopLevel::TLShow(call)];
        let c = emit_c(tops, &[]);
        assert!(c.contains("s("));
    }

    #[test]
    fn emit_let_str_printf_format() {
        let (_b, arena) = setup();
        let term = arena.let_(
            arena.alloc_str("s"),
            arena.lit_str(arena.alloc_str("hi")),
            arena.var(0),
            None,
        );
        let c = emit_c(&[TopLevel::TLShow(term)], &[]);
        assert!(c.contains("%s"));
        assert!(c.contains("const char* s"));
    }

    #[test]
    fn emit_multiple_defs_and_outputs() {
        let (_b, arena) = setup();
        let tops = &[
            TopLevel::TLDef(arena.alloc_str("a"), arena.lit_int(1)),
            TopLevel::TLDef(arena.alloc_str("b"), arena.lit_str(arena.alloc_str("two"))),
            TopLevel::TLShow(arena.lit_int(3)),
            TopLevel::TLShow(arena.lit_str(arena.alloc_str("four"))),
        ];
        let c = emit_c(tops, &[]);
        assert!(c.contains("const int64_t a = 1;"));
        assert!(c.contains("const char* b = \"two\";"));
        assert!(c.contains("%ld"));
        assert!(c.contains("%s"));
    }
}
