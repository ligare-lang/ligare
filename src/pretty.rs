use crate::core::syntax::{Name, PrimOp, Term};

/// Pretty-printer for Terms, producing human-readable string representations.
///
/// Encapsulates formatting logic as methods on a struct that can be
/// extended with configuration options (indentation, colors, etc.).
pub struct PrettyPrinter;

impl PrettyPrinter {
    /// Format a single term to a string.
    pub fn pretty(t: &Term<'_>) -> String {
        match t {
            Term::Var(i) => format!("${}", i),
            Term::Lam(body) => format!("λ. {}", Self::pretty(body)),
            Term::App(f, a) => Self::pretty_app(f, a),
            Term::LitInt(n) => n.to_string(),
            Term::Universe(u) => u.to_string(),
            Term::Pi("", a, b) => {
                format!("({} -> {})", Self::pretty(a), Self::pretty(b))
            }
            Term::Pi(name, a, b) => {
                format!("(Pi {} : {} => {})", name, Self::pretty(a), Self::pretty(b))
            }
            Term::Builtin(s) => (*s).to_string(),
            Term::PrimOp(op) => op.to_string(),
            Term::LitBool(b) => b.to_string(),
            Term::Let(name, val, body, mconstr) => {
                let constr_str = match mconstr {
                    Some(c) => format!(" : {}", Self::pretty(c)),
                    None => String::new(),
                };
                format!(
                    "let {}{} = {} in {}",
                    name,
                    constr_str,
                    Self::pretty(val),
                    Self::pretty(body)
                )
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                format!(
                    "if {} then {} else {}",
                    Self::pretty(cond),
                    Self::pretty(tbranch),
                    Self::pretty(fbranch)
                )
            }
            Term::Refine(_name, parent, p) => {
                format!("{} where (x => {})", Self::pretty(parent), Self::pretty(p))
            }
            Term::Annot(inner, c) => {
                format!("({} : {})", Self::pretty(inner), Self::pretty(c))
            }
            Term::ByProof(inner, proof) => {
                format!("({} by {})", Self::pretty(inner), Self::pretty(proof))
            }
            Term::AutoProof => "auto".to_string(),
            Term::RefParam => "x".to_string(),
            Term::This => "this".to_string(),
            Term::ProofBlock(inner) => {
                format!("proof {{ {} }}", Self::pretty(inner))
            }
            Term::Func(name, params, m_ret, preconds, postconds, body) => {
                let params_str = Self::pretty_params(params);
                let ret_str = m_ret
                    .map(|r| format!(" : {}", Self::pretty(r)))
                    .unwrap_or_default();
                let pre_str: String = preconds
                    .iter()
                    .map(|p| format!(" pre: {}", Self::pretty(p)))
                    .collect();
                let post_str: String = postconds
                    .iter()
                    .map(|p| format!(" post: {}", Self::pretty(p)))
                    .collect();
                format!(
                    "func {}({}){}{}{} = {}",
                    name,
                    params_str,
                    ret_str,
                    pre_str,
                    post_str,
                    Self::pretty(body)
                )
            }
        }
    }

    /// Pretty-print an application, using infix notation for binary operators
    /// and unary notation for negation.
    fn pretty_app(f: &Term<'_>, a: &Term<'_>) -> String {
        // Detect binary operator: ((op left) right)
        if let Term::App(inner, left) = f {
            if matches!(inner, Term::PrimOp(_)) {
                // Special case: unary negation (0 - x)
                if is_sub(inner) && matches!(left, Term::LitInt(0)) {
                    return Self::pretty_neg(a);
                }
                // General infix: (left op right)
                return format!(
                    "({} {} {})",
                    Self::pretty(left),
                    Self::pretty(inner),
                    Self::pretty(a)
                );
            }
        }
        // Default: prefix application
        format!("({} {})", Self::pretty(f), Self::pretty(a))
    }

    /// Format a negated term: `-lit` for simple atoms, `-(expr)` for complex ones.
    fn pretty_neg(t: &Term<'_>) -> String {
        let inner = Self::pretty(t);
        match t {
            // Simple atoms don't need parentheses around the operand
            Term::LitInt(_)
            | Term::LitBool(_)
            | Term::Builtin(_)
            | Term::Var(_)
            | Term::This
            | Term::RefParam
            | Term::AutoProof => format!("-{}", inner),
            // Complex sub-terms wrap in parens for clarity
            _ => format!("-({})", inner),
        }
    }

    /// Format parameter list: `(name : type, ...)`.
    fn pretty_params(params: &[(Name<'_>, Option<&Term<'_>>)]) -> String {
        params
            .iter()
            .map(|(n, mc)| match mc {
                Some(c) => format!("{} : {}", n, Self::pretty(c)),
                None => (*n).to_string(),
            })
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn pretty(t: &Term<'_>) -> String {
    PrettyPrinter::pretty(t)
}

// ── helpers ──

fn is_sub(t: &Term<'_>) -> bool {
    matches!(t, Term::PrimOp(PrimOp::Sub))
}
