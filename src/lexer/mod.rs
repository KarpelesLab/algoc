//! Lexer module for AlgoC
//!
//! Hand-written lexer that tokenizes AlgoC source code into a stream of tokens.

mod token;
mod scanner;

pub use token::{Token, TokenKind, Keyword};
pub use scanner::Lexer;
