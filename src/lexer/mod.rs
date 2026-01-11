//! Lexer module for AlgoC
//!
//! Hand-written lexer that tokenizes AlgoC source code into a stream of tokens.

mod scanner;
mod token;

pub use scanner::Lexer;
pub use token::{Keyword, Token, TokenKind};
