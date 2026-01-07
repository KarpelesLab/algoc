//! Parser module for AlgoC
//!
//! Hand-written recursive descent parser that produces an AST.

mod ast;
mod parser;

pub use ast::*;
pub use parser::Parser;
