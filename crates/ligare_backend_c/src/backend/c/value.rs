//! Internal value objects shared by C backend emitters.

use crate::backend::ir::CType;
use crate::diagnostic::Diagnostic;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CCode(String);

impl CCode {
    pub fn new(code: impl Into<String>) -> Self {
        Self(code.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Clone, Debug)]
pub enum CExpr {
    Code(CCode),
    Match(MatchPlan),
}

impl CExpr {
    pub fn code(self) -> Result<CCode, Diagnostic> {
        match self {
            CExpr::Code(code) => Ok(code),
            CExpr::Match(_) => Err(Diagnostic::new(
                "Nested match expression cannot be embedded as plain C expression",
            )),
        }
    }

    pub fn as_code(&self) -> Result<&CCode, Diagnostic> {
        match self {
            CExpr::Code(code) => Ok(code),
            CExpr::Match(_) => Err(Diagnostic::new(
                "Nested match expression cannot be embedded as plain C expression",
            )),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CValue {
    pub expr: CExpr,
    pub ctype: CType,
}

impl CValue {
    pub fn code(code: impl Into<String>, ctype: CType) -> Self {
        Self {
            expr: CExpr::Code(CCode::new(code)),
            ctype,
        }
    }

    pub fn match_(plan: MatchPlan) -> Self {
        let ctype = plan.ret_type.clone();
        Self {
            expr: CExpr::Match(plan),
            ctype,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MatchPlan {
    pub scrut_type: CType,
    pub scrut_code: CCode,
    pub ret_type: CType,
    pub cases: Vec<MatchCase>,
}

#[derive(Clone, Debug)]
pub struct MatchCase {
    pub variant_idx: usize,
    pub binds: Vec<MatchBind>,
    pub body_code: CCode,
}

#[derive(Clone, Debug)]
pub struct MatchBind {
    pub name: String,
    pub ctype: CType,
}
