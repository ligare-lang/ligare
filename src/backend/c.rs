//! C code generation backend.
//!
//! Generates straightforward C from Ligare terms, suitable for
//! compilation with any C compiler (cc, gcc, clang).

use crate::core::syntax::{PrimOp, Term};
use crate::front::parser::TopLevel;

/// Emit a complete C source file from a list of top-level items.
pub fn emit_c(tops: &[TopLevel<'_>]) -> String {
    let mut out = String::from("#include <stdio.h>\n#include <stdint.h>\n\n");
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
        out.push_str("int main(void) {\n");
        for term in &outputs {
            out.push_str(&format!(
                "    printf(\"%ld\\n\", (int64_t){});\n",
                emit_expr(term, &[], None)
            ));
        }
        out.push_str("    return 0;\n}\n");
    }
    out
}

fn emit_def(name: &str, term: &Term<'_>) -> String {
    let (body, params, self_name) = if let Term::Func(_, params, _, body) = term {
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
            return format!(
                "const int64_t {} = {};\n",
                name,
                emit_expr(inner, &[], None)
            );
        }
        let pns: Vec<String> = (0..arity).rev().map(|i| format!("arg_{}", i)).collect();
        (peel_lams(inner, arity), pns, None)
    };
    if params.is_empty() {
        return format!(
            "const int64_t {} = {};\n",
            name,
            emit_expr(body, &[], self_name)
        );
    }
    let cps: Vec<String> = params.iter().map(|p| format!("int64_t {p}")).collect();
    let bd: Vec<String> = params.iter().rev().cloned().collect();
    format!(
        "int64_t {}({}) {{\n    return {};\n}}\n",
        name,
        cps.join(", "),
        emit_expr(body, &bd, self_name)
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

/// Emit a term as a C expression.
fn emit_expr(term: &Term<'_>, bound: &[String], self_name: Option<&str>) -> String {
    match term {
        Term::LitInt(n) => n.to_string(),
        Term::LitBool(b) => {
            if *b {
                "1".into()
            } else {
                "0".into()
            }
        }
        Term::Var(i) => bound[*i].clone(),
        Term::This => self_name.unwrap_or("__self__").to_string(),
        Term::Builtin(name) => (*name).to_string(),
        Term::Annot(inner, _) => emit_expr(inner, bound, self_name),
        Term::ByProof(Some(inner), _) => emit_expr(inner, bound, self_name),
        Term::ByProof(None, _) => "0".into(),
        Term::IfThenElse(c, t, f) => format!(
            "({}) ? ({}) : ({})",
            emit_expr(c, bound, self_name),
            emit_expr(t, bound, self_name),
            emit_expr(f, bound, self_name)
        ),
        Term::Let(name, val, body, _) => {
            let v = emit_expr(val, bound, self_name);
            let mut ext: Vec<String> = vec![(*name).to_string()];
            ext.extend_from_slice(bound);
            format!(
                "({{ int64_t {} = {}; {}; }})",
                name,
                v,
                emit_expr(body, &ext, self_name)
            )
        }
        Term::App(_, _) => emit_app(term, bound, self_name),
        _ => "0".into(),
    }
}

fn emit_app(term: &Term<'_>, bound: &[String], self_name: Option<&str>) -> String {
    let Term::App(f, a) = term else {
        unreachable!()
    };
    // Binary operators.
    if let Term::App(prim, left) = f
        && let Term::PrimOp(op) = prim
    {
        return emit_binop(
            *op,
            &emit_expr(left, bound, self_name),
            &emit_expr(a, bound, self_name),
        );
    }
    if matches!(**f, Term::PrimOp(_)) {
        return emit_expr(a, bound, self_name);
    }
    // Function call.
    let mut args: Vec<String> = Vec::new();
    let func = collect_call_args(term, bound, &mut args, self_name);
    format!("{}({})", func, args.join(", "))
}

fn collect_call_args(
    term: &Term<'_>,
    bound: &[String],
    args: &mut Vec<String>,
    self_name: Option<&str>,
) -> String {
    match term {
        Term::App(f, a) => {
            let func = collect_call_args(f, bound, args, self_name);
            args.push(emit_expr(a, bound, self_name));
            func
        }
        _ => emit_expr(term, bound, self_name),
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
