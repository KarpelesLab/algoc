//! Semantic analysis for AlgoC
//!
//! This module handles name resolution, type checking, and semantic validation.

mod checker;
mod monomorphize;
mod resolver;
mod scope;
mod types;
mod validator;

pub use checker::TypeChecker;
pub use monomorphize::Monomorphizer;
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
    // Pass 1: Initial resolution (to get interface definitions for monomorphization)
    let resolver = Resolver::new();
    let initial_scope = resolver.resolve(&ast)?;

    // Pass 2: Monomorphize generic functions
    let monomorphizer = Monomorphizer::new(&initial_scope);
    let ast = monomorphizer.monomorphize(&ast)?;

    // Pass 3: Re-resolve to include generated functions in scope
    let resolver = Resolver::new();
    let global_scope = resolver.resolve(&ast)?;

    // Pass 4: Type check all expressions and statements
    let checker = TypeChecker::new(&global_scope);
    checker.check(&ast)?;

    // Pass 5: Semantic validation (break/continue in loops, etc.)
    let validator = Validator::new();
    validator.validate(&ast)?;

    Ok(AnalyzedAst { ast, global_scope })
}
