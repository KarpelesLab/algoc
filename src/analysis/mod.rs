//! Semantic analysis for AlgoC
//!
//! This module handles name resolution, type checking, and semantic validation.

mod checker;
mod resolver;
mod scope;
mod types;
mod validator;

pub use checker::TypeChecker;
pub use resolver::Resolver;
pub use scope::{Scope, Symbol, SymbolKind};
pub use types::{Type, TypeError, TypeKind};
pub use validator::Validator;

use crate::errors::AlgocResult;
use crate::parser::Ast;

/// Analyzed program with resolved types and symbols
#[derive(Debug)]
pub struct AnalyzedAst {
    pub ast: Ast,
    pub global_scope: Scope,
}

/// Run all analysis passes on the AST
pub fn analyze(ast: Ast) -> AlgocResult<AnalyzedAst> {
    // Pass 1: Resolve names and build symbol tables
    let resolver = Resolver::new();
    let global_scope = resolver.resolve(&ast)?;

    // Pass 2: Type check all expressions and statements
    let checker = TypeChecker::new(&global_scope);
    checker.check(&ast)?;

    // Pass 3: Semantic validation (break/continue in loops, etc.)
    let validator = Validator::new();
    validator.validate(&ast)?;

    Ok(AnalyzedAst { ast, global_scope })
}
