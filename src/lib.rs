//! AlgoC - Algorithm pseudocode to multi-language transpiler
//!
//! This crate provides a compiler for the AlgoC domain-specific language,
//! which can express algorithms (hashing, encryption, compression, etc.)
//! and transpile them to multiple target languages.

pub mod analysis;
pub mod codegen;
pub mod errors;
pub mod lexer;
pub mod parser;

// Re-export commonly used types
pub use analysis::{AnalyzedAst, analyze};
pub use codegen::{CodeGenerator, JavaScriptGenerator, PythonGenerator};
pub use errors::{AlgocError, AlgocResult, SourceSpan};
pub use lexer::{Lexer, Token, TokenKind};
pub use parser::{Ast, Parser};
