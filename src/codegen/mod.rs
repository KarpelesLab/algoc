//! Code generation for AlgoC
//!
//! This module provides code generators for various target languages.

mod c;
mod cpp;
mod dart;
mod go;
mod java;
mod javascript;
mod kotlin;
mod objc;
mod perl;
mod php;
mod python;
mod rust_gen;
mod swift;
mod verilog;
mod vhdl;

pub use c::CGenerator;
pub use cpp::CppGenerator;
pub use dart::DartGenerator;
pub use go::GoGenerator;
pub use java::JavaGenerator;
pub use javascript::JavaScriptGenerator;
pub use kotlin::KotlinGenerator;
pub use objc::ObjCGenerator;
pub use perl::PerlGenerator;
pub use php::PhpGenerator;
pub use python::PythonGenerator;
pub use rust_gen::RustGenerator;
pub use swift::SwiftGenerator;
pub use verilog::VerilogGenerator;
pub use vhdl::VhdlGenerator;

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
