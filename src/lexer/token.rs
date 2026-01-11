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
    Use,
    Fn,
    Struct,
    Layout,
    Enum,
    Const,
    Let,
    Mut,
    Test,
    Match,
    Impl,

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

    // Big-endian types
    U16Be,
    U32Be,
    U64Be,
    U128Be,
    I16Be,
    I32Be,
    I64Be,
    I128Be,

    // Little-endian types
    U16Le,
    U32Le,
    U64Le,
    U128Le,
    I16Le,
    I32Le,
    I64Le,
    I128Le,

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

    // Test helpers (these are still builtins for now)
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
            "use" => Some(Keyword::Use),
            "fn" => Some(Keyword::Fn),
            "struct" => Some(Keyword::Struct),
            "layout" => Some(Keyword::Layout),
            "enum" => Some(Keyword::Enum),
            "const" => Some(Keyword::Const),
            "let" => Some(Keyword::Let),
            "mut" => Some(Keyword::Mut),
            "test" => Some(Keyword::Test),
            "match" => Some(Keyword::Match),
            "impl" => Some(Keyword::Impl),

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

            // Big-endian types
            "u16be" => Some(Keyword::U16Be),
            "u32be" => Some(Keyword::U32Be),
            "u64be" => Some(Keyword::U64Be),
            "u128be" => Some(Keyword::U128Be),
            "i16be" => Some(Keyword::I16Be),
            "i32be" => Some(Keyword::I32Be),
            "i64be" => Some(Keyword::I64Be),
            "i128be" => Some(Keyword::I128Be),

            // Little-endian types
            "u16le" => Some(Keyword::U16Le),
            "u32le" => Some(Keyword::U32Le),
            "u64le" => Some(Keyword::U64Le),
            "u128le" => Some(Keyword::U128Le),
            "i16le" => Some(Keyword::I16Le),
            "i32le" => Some(Keyword::I32Le),
            "i64le" => Some(Keyword::I64Le),
            "i128le" => Some(Keyword::I128Le),

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

            // Test helpers
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
            Keyword::Use => "use",
            Keyword::Fn => "fn",
            Keyword::Struct => "struct",
            Keyword::Layout => "layout",
            Keyword::Enum => "enum",
            Keyword::Const => "const",
            Keyword::Let => "let",
            Keyword::Mut => "mut",
            Keyword::Test => "test",
            Keyword::Match => "match",
            Keyword::Impl => "impl",
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
            Keyword::U16Be => "u16be",
            Keyword::U32Be => "u32be",
            Keyword::U64Be => "u64be",
            Keyword::U128Be => "u128be",
            Keyword::I16Be => "i16be",
            Keyword::I32Be => "i32be",
            Keyword::I64Be => "i64be",
            Keyword::I128Be => "i128be",
            Keyword::U16Le => "u16le",
            Keyword::U32Le => "u32le",
            Keyword::U64Le => "u64le",
            Keyword::U128Le => "u128le",
            Keyword::I16Le => "i16le",
            Keyword::I32Le => "i32le",
            Keyword::I64Le => "i64le",
            Keyword::I128Le => "i128le",
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
    /// `::`
    ColonColon,
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
    /// `=>`
    FatArrow,
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
            TokenKind::ColonColon => "'::'",
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
            TokenKind::FatArrow => "'=>'",
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
