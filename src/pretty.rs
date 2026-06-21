use crate::core::syntax::{PrimOp, Tactic, Term};

pub struct PrettyPrinter;

impl PrettyPrinter {
    pub fn pretty(t: &Term<'_>) -> String {
        match t {
            Term::Var(i) => format!("${}", i),
            Term::Lam(body) => format!("λ. {}", Self::pretty(body)),
            Term::App(f, a) => Self::pretty_app(f, a),
            Term::LitInt(n) => n.to_string(),
            Term::Universe(u) => u.to_string(),
            Term::Pi("", a, b) => format!("({} -> {})", Self::pretty(a), Self::pretty(b)),
            Term::Pi(name, a, b) => {
                format!("(Pi {} : {} => {})", name, Self::pretty(a), Self::pretty(b))
            }
            Term::Builtin(s) => (*s).to_string(),
            Term::PrimOp(op) => op.to_string(),
            Term::LitBool(b) => b.to_string(),
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
            Term::This => "this".to_string(),
            Term::Func(name, params, m_ret, body) => {
                let ps: String = params
                    .iter()
                    .map(|(n, mc)| match mc {
                        Some(c) => format!("{} : {}", n, Self::pretty(c)),
                        None => (*n).to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let rs = m_ret.map_or(String::new(), |r| format!(" : {}", Self::pretty(r)));
                format!("func {}({}){} = {}", name, ps, rs, Self::pretty(body))
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
            | Term::Var(_)
            | Term::This
            | Term::RefParam
            | Term::AutoProof => format!("-{}", inner),
            _ => format!("-({})", inner),
        }
    }
}

pub fn pretty(t: &Term<'_>) -> String {
    PrettyPrinter::pretty(t)
}
