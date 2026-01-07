//! Token definitions for AlgoC
//!
//! Defines all token types produced by the lexer.

use crate::errors::SourceSpan;
use std::fmt;

/// A token produced by the lexer
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    /// The kind of token
    pub kind: TokenKind,
    /// Source location of this token
    pub span: SourceSpan,
}

impl Token {
    pub fn new(kind: TokenKind, span: SourceSpan) -> Self {
        Self { kind, span }
    }
}

/// Keywords in the AlgoC language
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Keyword {
    // Declarations
    Fn,
    Struct,
    Layout,
    Const,
    Let,
    Mut,
    Test,

    // Types
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    Bool,

    // Control flow
    If,
    Else,
    For,
    While,
    Loop,
    Break,
    Continue,
    Return,
    In,

    // Boolean literals
    True,
    False,

    // Modifiers / Attributes
    BigEndian,
    LittleEndian,
    Aligned,
    Packed,

    // Built-in functions (recognized as keywords)
    Rotr,
    Rotl,
    Bswap,
    ReadU8,
    ReadU16Be,
    ReadU16Le,
    ReadU32Be,
    ReadU32Le,
    ReadU64Be,
    ReadU64Le,
    WriteU8,
    WriteU16Be,
    WriteU16Le,
    WriteU32Be,
    WriteU32Le,
    WriteU64Be,
    WriteU64Le,
    ConstantTimeEq,
    SecureZero,

    // Test helpers
    Input,
    Assert,
    Bytes,
    Hex,

    // Other
    As,
    Bits,
}

impl Keyword {
    /// Try to parse a string as a keyword
    pub fn from_str(s: &str) -> Option<Keyword> {
        match s {
            // Declarations
            "fn" => Some(Keyword::Fn),
            "struct" => Some(Keyword::Struct),
            "layout" => Some(Keyword::Layout),
            "const" => Some(Keyword::Const),
            "let" => Some(Keyword::Let),
            "mut" => Some(Keyword::Mut),
            "test" => Some(Keyword::Test),

            // Types
            "u8" => Some(Keyword::U8),
            "u16" => Some(Keyword::U16),
            "u32" => Some(Keyword::U32),
            "u64" => Some(Keyword::U64),
            "u128" => Some(Keyword::U128),
            "i8" => Some(Keyword::I8),
            "i16" => Some(Keyword::I16),
            "i32" => Some(Keyword::I32),
            "i64" => Some(Keyword::I64),
            "i128" => Some(Keyword::I128),
            "bool" => Some(Keyword::Bool),

            // Control flow
            "if" => Some(Keyword::If),
            "else" => Some(Keyword::Else),
            "for" => Some(Keyword::For),
            "while" => Some(Keyword::While),
            "loop" => Some(Keyword::Loop),
            "break" => Some(Keyword::Break),
            "continue" => Some(Keyword::Continue),
            "return" => Some(Keyword::Return),
            "in" => Some(Keyword::In),

            // Booleans
            "true" => Some(Keyword::True),
            "false" => Some(Keyword::False),

            // Modifiers
            "big_endian" => Some(Keyword::BigEndian),
            "little_endian" => Some(Keyword::LittleEndian),
            "aligned" => Some(Keyword::Aligned),
            "packed" => Some(Keyword::Packed),

            // Built-ins
            "rotr" => Some(Keyword::Rotr),
            "rotl" => Some(Keyword::Rotl),
            "bswap" => Some(Keyword::Bswap),
            "read_u8" => Some(Keyword::ReadU8),
            "read_u16_be" => Some(Keyword::ReadU16Be),
            "read_u16_le" => Some(Keyword::ReadU16Le),
            "read_u32_be" => Some(Keyword::ReadU32Be),
            "read_u32_le" => Some(Keyword::ReadU32Le),
            "read_u64_be" => Some(Keyword::ReadU64Be),
            "read_u64_le" => Some(Keyword::ReadU64Le),
            "write_u8" => Some(Keyword::WriteU8),
            "write_u16_be" => Some(Keyword::WriteU16Be),
            "write_u16_le" => Some(Keyword::WriteU16Le),
            "write_u32_be" => Some(Keyword::WriteU32Be),
            "write_u32_le" => Some(Keyword::WriteU32Le),
            "write_u64_be" => Some(Keyword::WriteU64Be),
            "write_u64_le" => Some(Keyword::WriteU64Le),
            "constant_time_eq" => Some(Keyword::ConstantTimeEq),
            "secure_zero" => Some(Keyword::SecureZero),

            // Test helpers
            "input" => Some(Keyword::Input),
            "assert" => Some(Keyword::Assert),
            "bytes" => Some(Keyword::Bytes),
            "hex" => Some(Keyword::Hex),

            // Other
            "as" => Some(Keyword::As),
            "bits" => Some(Keyword::Bits),

            _ => None,
        }
    }
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Keyword::Fn => "fn",
            Keyword::Struct => "struct",
            Keyword::Layout => "layout",
            Keyword::Const => "const",
            Keyword::Let => "let",
            Keyword::Mut => "mut",
            Keyword::Test => "test",
            Keyword::U8 => "u8",
            Keyword::U16 => "u16",
            Keyword::U32 => "u32",
            Keyword::U64 => "u64",
            Keyword::U128 => "u128",
            Keyword::I8 => "i8",
            Keyword::I16 => "i16",
            Keyword::I32 => "i32",
            Keyword::I64 => "i64",
            Keyword::I128 => "i128",
            Keyword::Bool => "bool",
            Keyword::If => "if",
            Keyword::Else => "else",
            Keyword::For => "for",
            Keyword::While => "while",
            Keyword::Loop => "loop",
            Keyword::Break => "break",
            Keyword::Continue => "continue",
            Keyword::Return => "return",
            Keyword::In => "in",
            Keyword::True => "true",
            Keyword::False => "false",
            Keyword::BigEndian => "big_endian",
            Keyword::LittleEndian => "little_endian",
            Keyword::Aligned => "aligned",
            Keyword::Packed => "packed",
            Keyword::Rotr => "rotr",
            Keyword::Rotl => "rotl",
            Keyword::Bswap => "bswap",
            Keyword::ReadU8 => "read_u8",
            Keyword::ReadU16Be => "read_u16_be",
            Keyword::ReadU16Le => "read_u16_le",
            Keyword::ReadU32Be => "read_u32_be",
            Keyword::ReadU32Le => "read_u32_le",
            Keyword::ReadU64Be => "read_u64_be",
            Keyword::ReadU64Le => "read_u64_le",
            Keyword::WriteU8 => "write_u8",
            Keyword::WriteU16Be => "write_u16_be",
            Keyword::WriteU16Le => "write_u16_le",
            Keyword::WriteU32Be => "write_u32_be",
            Keyword::WriteU32Le => "write_u32_le",
            Keyword::WriteU64Be => "write_u64_be",
            Keyword::WriteU64Le => "write_u64_le",
            Keyword::ConstantTimeEq => "constant_time_eq",
            Keyword::SecureZero => "secure_zero",
            Keyword::Input => "input",
            Keyword::Assert => "assert",
            Keyword::Bytes => "bytes",
            Keyword::Hex => "hex",
            Keyword::As => "as",
            Keyword::Bits => "bits",
        };
        write!(f, "{}", s)
    }
}

/// The kind of a token
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    /// Integer literal (decimal, hex, binary, or octal)
    Integer(u128),
    /// String literal
    String(String),
    /// Identifier
    Ident(String),
    /// Keyword
    Keyword(Keyword),

    // Punctuation - single character
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `;`
    Semicolon,
    /// `:`
    Colon,
    /// `,`
    Comma,
    /// `.`
    Dot,
    /// `@`
    At,

    // Operators - single character
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Star,
    /// `/`
    Slash,
    /// `%`
    Percent,
    /// `&`
    Amp,
    /// `|`
    Pipe,
    /// `^`
    Caret,
    /// `~`
    Tilde,
    /// `!`
    Bang,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `=`
    Eq,

    // Operators - multi character
    /// `==`
    EqEq,
    /// `!=`
    BangEq,
    /// `<=`
    LtEq,
    /// `>=`
    GtEq,
    /// `<<`
    LtLt,
    /// `>>`
    GtGt,
    /// `&&`
    AmpAmp,
    /// `||`
    PipePipe,
    /// `+=`
    PlusEq,
    /// `-=`
    MinusEq,
    /// `*=`
    StarEq,
    /// `/=`
    SlashEq,
    /// `%=`
    PercentEq,
    /// `&=`
    AmpEq,
    /// `|=`
    PipeEq,
    /// `^=`
    CaretEq,
    /// `<<=`
    LtLtEq,
    /// `>>=`
    GtGtEq,
    /// `->`
    Arrow,
    /// `..`
    DotDot,
    /// `..=`
    DotDotEq,

    // Special
    /// End of file
    Eof,
    /// Error token (lexer error, but we keep going)
    Error(String),
}

impl TokenKind {
    /// Check if this is an EOF token
    pub fn is_eof(&self) -> bool {
        matches!(self, TokenKind::Eof)
    }

    /// Check if this is an error token
    pub fn is_error(&self) -> bool {
        matches!(self, TokenKind::Error(_))
    }

    /// Get a human-readable description of this token kind
    pub fn description(&self) -> &'static str {
        match self {
            TokenKind::Integer(_) => "integer literal",
            TokenKind::String(_) => "string literal",
            TokenKind::Ident(_) => "identifier",
            TokenKind::Keyword(_) => "keyword",
            TokenKind::LParen => "'('",
            TokenKind::RParen => "')'",
            TokenKind::LBrace => "'{'",
            TokenKind::RBrace => "'}'",
            TokenKind::LBracket => "'['",
            TokenKind::RBracket => "']'",
            TokenKind::Semicolon => "';'",
            TokenKind::Colon => "':'",
            TokenKind::Comma => "','",
            TokenKind::Dot => "'.'",
            TokenKind::At => "'@'",
            TokenKind::Plus => "'+'",
            TokenKind::Minus => "'-'",
            TokenKind::Star => "'*'",
            TokenKind::Slash => "'/'",
            TokenKind::Percent => "'%'",
            TokenKind::Amp => "'&'",
            TokenKind::Pipe => "'|'",
            TokenKind::Caret => "'^'",
            TokenKind::Tilde => "'~'",
            TokenKind::Bang => "'!'",
            TokenKind::Lt => "'<'",
            TokenKind::Gt => "'>'",
            TokenKind::Eq => "'='",
            TokenKind::EqEq => "'=='",
            TokenKind::BangEq => "'!='",
            TokenKind::LtEq => "'<='",
            TokenKind::GtEq => "'>='",
            TokenKind::LtLt => "'<<'",
            TokenKind::GtGt => "'>>'",
            TokenKind::AmpAmp => "'&&'",
            TokenKind::PipePipe => "'||'",
            TokenKind::PlusEq => "'+='",
            TokenKind::MinusEq => "'-='",
            TokenKind::StarEq => "'*='",
            TokenKind::SlashEq => "'/='",
            TokenKind::PercentEq => "'%='",
            TokenKind::AmpEq => "'&='",
            TokenKind::PipeEq => "'|='",
            TokenKind::CaretEq => "'^='",
            TokenKind::LtLtEq => "'<<='",
            TokenKind::GtGtEq => "'>>='",
            TokenKind::Arrow => "'->'",
            TokenKind::DotDot => "'..'",
            TokenKind::DotDotEq => "'..='",
            TokenKind::Eof => "end of file",
            TokenKind::Error(_) => "error",
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Integer(n) => write!(f, "{}", n),
            TokenKind::String(s) => write!(f, "\"{}\"", s),
            TokenKind::Ident(s) => write!(f, "{}", s),
            TokenKind::Keyword(kw) => write!(f, "{}", kw),
            _ => write!(f, "{}", self.description()),
        }
    }
}
