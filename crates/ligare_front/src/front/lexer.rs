use logos::Logos;

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
#[logos(skip r"[ \t\r\f]+")]
#[logos(skip r"--[^\n]*")]
#[logos(skip r"\{-([^-]|-[^}])*-\}")]
pub enum Token {
    // Whitespace
    #[token("\n")]
    Newline,
    // Keywords
    #[token("let")]
    KwLet,
    #[token("in")]
    KwIn,
    #[token("if")]
    KwIf,
    #[token("then")]
    KwThen,
    #[token("else")]
    KwElse,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("by")]
    KwBy,
    #[token("fun")]
    KwFun,
    #[token("func")]
    KwFunc,
    #[token("do")]
    KwDo,
    #[token("where")]
    KwWhere,
    #[token("def")]
    KwDef,
    #[token("extern")]
    KwExtern,
    #[token("instance")]
    KwInstance,
    #[token("variable")]
    KwVariable,
    #[token("unsafe")]
    KwUnsafe,
    #[token("pure")]
    KwPure,
    #[token("auto")]
    KwAuto,
    #[token("exact")]
    KwExact,
    #[token("apply")]
    KwApply,
    #[token("intro")]
    KwIntro,
    #[token("have")]
    KwHave,
    #[token("theorem")]
    KwTheorem,
    #[token("pub")]
    KwPub,
    #[token("use")]
    KwUse,
    #[token("mod")]
    KwMod,
    #[token("namespace")]
    KwNamespace,
    #[token("as")]
    KwAs,

    // Enum / Struct keywords
    #[token("struct")]
    KwStruct,
    #[token("enum")]
    KwEnum,
    #[token("match")]
    KwMatch,
    #[token("with")]
    KwWith,
    #[token("of")]
    KwOf,
    #[token("|")]
    Bar,

    // Directives
    #[token("#[")]
    HashLBracket,
    #[token("#check")]
    HashCheck,
    #[token("#eval")]
    HashEval,

    // Nestable block comment (Lean 4 style: /- ... -/)
    #[token("/-", nestable_block_comment)]
    BlockComment,

    // Symbols
    #[token(":=")]
    ColonEq,
    #[token("::")]
    PathSep,
    #[token("=>")]
    FatArrow,
    #[token("->")]
    ThinArrow,
    #[token("<=")]
    Le,
    #[token("<-")]
    LeftArrow,
    #[token(">=")]
    Ge,
    #[token("/=")]
    Neq,
    #[token("==")]
    EqEq,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("]")]
    RBracket,
    #[token(";")]
    Semi,
    #[token(",")]
    Comma,
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(":")]
    Colon,
    #[token(".")]
    Dot,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("$")]
    Dollar,
    #[token("<")]
    Lt,
    #[token(">")]
    Gt,
    #[token("=")]
    Eq,
    #[token("∧")]
    And,
    #[token("∨")]
    Or,
    #[token("¬")]
    Not,
    #[token("→")]
    Implies,

    // Compound Unicode builtins
    #[token("∧-intro")]
    AndIntro,
    #[token("∧-elim-left")]
    AndElimLeft,

    // Literals
    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i64>().ok())]
    IntLit(i64),

    /// String literal: `"..."` — the captured slice excludes the surrounding quotes.
    #[regex(r#""([^"\\]|\\.)*""#, |lex| {
        let raw = lex.slice();
        // Strip surrounding quotes and unescape
        let inner = &raw[1..raw.len()-1];
        inner.to_string()
    })]
    StrLit(String),

    // Identifier: starts with letter, followed by alphanumerics or underscore
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
}

/// Nestable block comment `/- ... -/` (Lean 4 style).
///
/// Called by the lexer when `/-` is encountered.  Scans forward
/// tracking nesting depth so that `/- outer /- inner -/ -/`
/// is a single comment.
fn nestable_block_comment(lex: &mut logos::Lexer<Token>) {
    let mut depth: u32 = 1;
    let rest = lex.remainder();
    let bytes = rest.as_bytes();
    let mut i = 0;
    while i + 1 < bytes.len() {
        if bytes[i] == b'/' && bytes[i + 1] == b'-' {
            depth += 1;
            i += 2;
        } else if bytes[i] == b'-' && bytes[i + 1] == b'/' {
            depth -= 1;
            if depth == 0 {
                lex.bump(i + 2); // skip past closing `-/`
                return;
            }
            i += 2;
        } else {
            i += 1;
        }
    }
    // Unterminated comment — consume the rest
    lex.bump(rest.len());
}
