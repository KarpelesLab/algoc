//! Code generation for AlgoC
//!
//! This module provides code generators for various target languages.

mod javascript;

pub use javascript::JavaScriptGenerator;

use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;

/// Trait for code generators
pub trait CodeGenerator {
    /// Generate code from the analyzed AST
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String>;

    /// Get the file extension for the target language
    fn file_extension(&self) -> &'static str;

    /// Get the name of the target language
    fn language_name(&self) -> &'static str;
}
