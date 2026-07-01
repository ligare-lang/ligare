use crate::core::syntax::{PrimOp, Tactic, Term};

pub struct PrettyPrinter;

impl PrettyPrinter {
    pub fn pretty(t: &Term<'_>) -> String {
        match t {
            Term::Var(i) => format!("${}", i),
            Term::Lam(body) => format!("λ. {}", Self::pretty(body)),
            Term::NamedLam(name, body) => {
                format!("fun {} => {}", name, Self::pretty(body))
            }
            Term::App(f, a) => Self::pretty_app(f, a),
            Term::LitInt(n) => n.to_string(),
            Term::Universe(u) => u.to_string(),
            Term::Pi("", a, b) => format!("({} -> {})", Self::pretty(a), Self::pretty(b)),
            Term::Pi(name, a, b) => {
                format!("(Pi {} : {} => {})", name, Self::pretty(a), Self::pretty(b))
            }
            Term::Builtin(s) | Term::Named(s) | Term::Global(s) => (*s).to_string(),
            Term::PrimOp(op) => op.to_string(),
            Term::LitBool(b) => b.to_string(),
            Term::LitStr(s) => format!("\"{}\"", s),
            Term::Let(name, val, body, mconstr) => {
                let c = mconstr.map_or(String::new(), |c| format!(" : {}", Self::pretty(c)));
                format!(
                    "let {}{} = {} in {}",
                    name,
                    c,
                    Self::pretty(val),
                    Self::pretty(body)
                )
            }
            Term::IfThenElse(cond, t, f) => {
                format!(
                    "if {} then {} else {}",
                    Self::pretty(cond),
                    Self::pretty(t),
                    Self::pretty(f)
                )
            }
            Term::Refine(_, parent, p) => {
                format!("{} where (x => {})", Self::pretty(parent), Self::pretty(p))
            }
            Term::Annot(inner, c) => format!("({} : {})", Self::pretty(inner), Self::pretty(c)),
            Term::ByProof(inner, tactics) => {
                let ts: Vec<String> = tactics
                    .iter()
                    .map(|tac| match tac {
                        Tactic::Exact(t) => format!("exact {}", Self::pretty(t)),
                        Tactic::Apply(t) => format!("apply {}", Self::pretty(t)),
                        Tactic::Intro(Some(n)) => format!("intro {}", n),
                        Tactic::Intro(None) => "intro".to_string(),
                        Tactic::Have(n, t) => {
                            format!("have {} := {}", n, Self::pretty(t))
                        }
                    })
                    .collect();
                match inner {
                    Some(t) => format!("({} by {})", Self::pretty(t), ts.join("; ")),
                    None => format!("(by {})", ts.join("; ")),
                }
            }
            Term::AutoProof => "auto".to_string(),
            Term::RefParam => "x".to_string(),
            Term::UnionDef(name, variants) => {
                let vs: Vec<String> = variants
                    .iter()
                    .map(|(vn, fields)| {
                        if fields.is_empty() {
                            format!("| {}", vn)
                        } else {
                            let fs: Vec<String> = fields
                                .iter()
                                .map(|(fnm, fc)| format!("({} : {})", fnm, Self::pretty(fc)))
                                .collect();
                            format!("| {} of {}", vn, fs.join(" "))
                        }
                    })
                    .collect();
                format!("union {}\n  {}", name, vs.join("\n  "))
            }
            Term::Variant(name, _idx, payloads) => {
                let ps: Vec<String> = payloads.iter().map(|p| Self::pretty(p)).collect();
                format!("({}.{} {})", name, "variant", ps.join(" "))
            }
            Term::Match(scrut, branches) => {
                let bs: Vec<String> = branches
                    .iter()
                    .map(|(_idx, binds, body)| {
                        let bpat: Vec<String> = binds.iter().map(|(n, _)| n.to_string()).collect();
                        format!("| {} => {}", bpat.join(" "), Self::pretty(body))
                    })
                    .collect();
                format!("match {} with\n  {}", Self::pretty(scrut), bs.join("\n  "))
            }
            Term::NamedMatch(scrut, branches) => {
                let bs: Vec<String> = branches
                    .iter()
                    .map(|(variant, binds, body)| {
                        let bpat: Vec<String> = binds.iter().map(|(n, _)| n.to_string()).collect();
                        let payload = if bpat.is_empty() {
                            String::new()
                        } else {
                            format!(" {}", bpat.join(" "))
                        };
                        format!("| {variant}{payload} => {}", Self::pretty(body))
                    })
                    .collect();
                format!("match {} with\n  {}", Self::pretty(scrut), bs.join("\n  "))
            }
            Term::Do(stmts) => {
                let ss: Vec<String> = stmts
                    .iter()
                    .map(|stmt| match stmt {
                        crate::core::syntax::DoStmt::Bind(n, rhs) => {
                            format!("{} <- {}", n, Self::pretty(rhs))
                        }
                        crate::core::syntax::DoStmt::Let(n, rhs, mc) => {
                            let c = mc.map_or(String::new(), |c| format!(" : {}", Self::pretty(c)));
                            format!("let {}{} := {}", n, c, Self::pretty(rhs))
                        }
                        crate::core::syntax::DoStmt::Expr(expr) => Self::pretty(expr),
                    })
                    .collect();
                format!("do {{ {} }}", ss.join("; "))
            }
            Term::StructDef(name, fields) => {
                let fs: Vec<String> = fields
                    .iter()
                    .map(|(fnm, fc)| format!("{} : {}", fnm, Self::pretty(fc)))
                    .collect();
                format!("struct {}\n  {}", name, fs.join("\n  "))
            }
            Term::StructCons(name, field_values) => {
                let vs: Vec<String> = field_values.iter().map(|v| Self::pretty(v)).collect();
                format!("({}.mk {})", name, vs.join(" "))
            }
            Term::StructProj(subject, idx) => {
                format!("({}._{})", Self::pretty(subject), idx)
            }
        }
    }

    fn pretty_app(f: &Term<'_>, a: &Term<'_>) -> String {
        if let Term::App(inner, left) = f
            && matches!(inner, Term::PrimOp(_))
        {
            if matches!(inner, Term::PrimOp(PrimOp::Sub)) && matches!(left, Term::LitInt(0)) {
                return Self::pretty_neg(a);
            }
            return format!(
                "({} {} {})",
                Self::pretty(left),
                Self::pretty(inner),
                Self::pretty(a)
            );
        }
        format!("({} {})", Self::pretty(f), Self::pretty(a))
    }

    fn pretty_neg(t: &Term<'_>) -> String {
        let inner = Self::pretty(t);
        match t {
            Term::LitInt(_)
            | Term::LitBool(_)
            | Term::Builtin(_)
            | Term::Named(_)
            | Term::Global(_)
            | Term::NamedLam(_, _)
            | Term::Var(_)
            | Term::RefParam
            | Term::AutoProof => format!("-{}", inner),
            _ => format!("-({})", inner),
        }
    }
}

pub fn pretty(t: &Term<'_>) -> String {
    PrettyPrinter::pretty(t)
}
