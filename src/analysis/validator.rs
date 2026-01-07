//! Semantic validation pass
//!
//! Checks semantic rules that aren't covered by type checking.

use crate::errors::{AlgocError, AlgocResult, SourceSpan};
use crate::parser::{Ast, Item, ItemKind, Stmt, StmtKind, Block};

/// Semantic validator
pub struct Validator {
    /// Current loop nesting depth
    loop_depth: u32,
    /// Collected errors
    errors: Vec<AlgocError>,
}

impl Validator {
    pub fn new() -> Self {
        Self {
            loop_depth: 0,
            errors: Vec::new(),
        }
    }

    /// Validate the AST
    pub fn validate(mut self, ast: &Ast) -> AlgocResult<()> {
        for item in &ast.items {
            self.validate_item(item);
        }

        if !self.errors.is_empty() {
            return Err(self.errors.remove(0));
        }

        Ok(())
    }

    fn error(&mut self, message: impl Into<String>, span: SourceSpan) {
        self.errors.push(AlgocError::semantic(message, span));
    }

    fn validate_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => {
                self.validate_block(&func.body);
            }
            ItemKind::Const(_) => {
                // Constants are validated by type checker
            }
            ItemKind::Test(test) => {
                // Validate test body like a function
                self.validate_block(&test.body);
            }
            ItemKind::Struct(_) | ItemKind::Layout(_) => {
                // Type definitions don't need validation
            }
        }
    }

    fn validate_block(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.validate_stmt(stmt);
        }
    }

    fn validate_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Break => {
                if self.loop_depth == 0 {
                    self.error("break outside of loop", stmt.span);
                }
            }
            StmtKind::Continue => {
                if self.loop_depth == 0 {
                    self.error("continue outside of loop", stmt.span);
                }
            }
            StmtKind::For { body, .. } => {
                self.loop_depth += 1;
                self.validate_block(body);
                self.loop_depth -= 1;
            }
            StmtKind::While { body, .. } => {
                self.loop_depth += 1;
                self.validate_block(body);
                self.loop_depth -= 1;
            }
            StmtKind::Loop { body } => {
                self.loop_depth += 1;
                self.validate_block(body);
                self.loop_depth -= 1;
            }
            StmtKind::If { then_block, else_block, .. } => {
                self.validate_block(then_block);
                if let Some(else_block) = else_block {
                    self.validate_block(else_block);
                }
            }
            StmtKind::Block(block) => {
                self.validate_block(block);
            }
            StmtKind::Let { .. } |
            StmtKind::Expr(_) |
            StmtKind::Assign { .. } |
            StmtKind::CompoundAssign { .. } |
            StmtKind::Return(_) => {
                // These don't need special validation
            }
        }
    }
}

impl Default for Validator {
    fn default() -> Self {
        Self::new()
    }
}
