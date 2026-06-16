use logos::Logos;

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
#[logos(skip r"[ \t\n\r\f]+")]
#[logos(skip r"--[^\n]*")]
#[logos(skip r"\{-([^-]|-[^}])*-\}")]
pub enum Token {
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
    #[token("func")]
    KwFunc,
    #[token("where")]
    KwWhere,
    #[token("def")]
    KwDef,
    #[token("auto")]
    KwAuto,

    // Directives
    #[token("#check")]
    HashCheck,
    #[token("#show")]
    HashShow,

    // Symbols
    #[token(":=")]
    ColonEq,
    #[token("=>")]
    FatArrow,
    #[token("->")]
    ThinArrow,
    #[token("<=")]
    Le,
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
    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token(":")]
    Colon,
    #[token(".")]
    Dot,
    #[token("\\")]
    Backslash,
    #[token("λ")]
    Lambda,
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

    // Identifier: starts with letter, followed by alphanumerics or underscore
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_]*", |lex| lex.slice().to_string())]
    Ident(String),
}
