//! Type checking pass
//!
//! Verifies that all expressions have compatible types.

use crate::errors::{AlgocError, AlgocResult, SourceSpan};
use crate::parser::{self, Ast, Item, ItemKind, BinaryOp, UnaryOp, BuiltinFunc, PrimitiveType as AstPrimitive};
use super::scope::{Scope, ScopeStack, Symbol, SymbolKind};
use super::types::{Type, TypeKind, Endianness};

/// Type checker that verifies type correctness
pub struct TypeChecker<'a> {
    /// The global scope from name resolution
    global_scope: &'a Scope,
    /// Current scope stack for local lookups
    scopes: ScopeStack,
    /// Current function's return type (for checking return statements)
    current_return_type: Option<Type>,
    /// Collected errors
    errors: Vec<AlgocError>,
}

impl<'a> TypeChecker<'a> {
    /// Create a new type checker
    pub fn new(global_scope: &'a Scope) -> Self {
        Self {
            global_scope,
            scopes: ScopeStack::new(),
            current_return_type: None,
            errors: Vec::new(),
        }
    }

    /// Type check the entire AST
    pub fn check(mut self, ast: &Ast) -> AlgocResult<()> {
        // Copy global symbols to local scope stack
        for (name, sym) in self.global_scope.symbols() {
            let _ = self.scopes.define(name.clone(), sym.clone());
        }

        for item in &ast.items {
            self.check_item(item);
        }

        if !self.errors.is_empty() {
            return Err(self.errors.remove(0));
        }

        Ok(())
    }

    /// Record an error
    fn error(&mut self, message: impl Into<String>, span: SourceSpan) {
        self.errors.push(AlgocError::type_error(message, span));
    }

    /// Convert an AST type to a checked type
    fn ast_to_type(&self, ty: &parser::Type) -> Type {
        match &ty.kind {
            parser::TypeKind::Primitive(p) => self.primitive_to_type(*p),
            parser::TypeKind::Array { element, size } => {
                Type::array(self.ast_to_type(element), *size)
            }
            parser::TypeKind::Slice { element } => {
                Type::slice(self.ast_to_type(element))
            }
            parser::TypeKind::ArrayRef { element, size } => {
                Type::reference(Type::array(self.ast_to_type(element), *size), false)
            }
            parser::TypeKind::MutRef(inner) => {
                Type::reference(self.ast_to_type(inner), true)
            }
            parser::TypeKind::Ref(inner) => {
                Type::reference(self.ast_to_type(inner), false)
            }
            parser::TypeKind::Named(ident) => {
                match ident.name.as_str() {
                    "Reader" => Type::reader(),
                    "Writer" => Type::writer(),
                    _ => Type::struct_type(ident.name.clone()),
                }
            }
        }
    }

    fn primitive_to_type(&self, p: AstPrimitive) -> Type {
        match p {
            // Native endian types
            AstPrimitive::U8 => Type::int(8, false),
            AstPrimitive::U16 => Type::int(16, false),
            AstPrimitive::U32 => Type::int(32, false),
            AstPrimitive::U64 => Type::int(64, false),
            AstPrimitive::U128 => Type::int(128, false),
            AstPrimitive::I8 => Type::int(8, true),
            AstPrimitive::I16 => Type::int(16, true),
            AstPrimitive::I32 => Type::int(32, true),
            AstPrimitive::I64 => Type::int(64, true),
            AstPrimitive::I128 => Type::int(128, true),
            AstPrimitive::Bool => Type::bool(),
            // Big-endian types
            AstPrimitive::U16Be => Type::int_endian(16, false, Endianness::Big),
            AstPrimitive::U32Be => Type::int_endian(32, false, Endianness::Big),
            AstPrimitive::U64Be => Type::int_endian(64, false, Endianness::Big),
            AstPrimitive::U128Be => Type::int_endian(128, false, Endianness::Big),
            AstPrimitive::I16Be => Type::int_endian(16, true, Endianness::Big),
            AstPrimitive::I32Be => Type::int_endian(32, true, Endianness::Big),
            AstPrimitive::I64Be => Type::int_endian(64, true, Endianness::Big),
            AstPrimitive::I128Be => Type::int_endian(128, true, Endianness::Big),
            // Little-endian types
            AstPrimitive::U16Le => Type::int_endian(16, false, Endianness::Little),
            AstPrimitive::U32Le => Type::int_endian(32, false, Endianness::Little),
            AstPrimitive::U64Le => Type::int_endian(64, false, Endianness::Little),
            AstPrimitive::U128Le => Type::int_endian(128, false, Endianness::Little),
            AstPrimitive::I16Le => Type::int_endian(16, true, Endianness::Little),
            AstPrimitive::I32Le => Type::int_endian(32, true, Endianness::Little),
            AstPrimitive::I64Le => Type::int_endian(64, true, Endianness::Little),
            AstPrimitive::I128Le => Type::int_endian(128, true, Endianness::Little),
        }
    }

    /// Check a top-level item
    fn check_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => {
                let return_type = func.return_type.as_ref()
                    .map(|t| self.ast_to_type(t))
                    .unwrap_or_else(Type::unit);
                self.current_return_type = Some(return_type);

                self.scopes.push();

                // Add parameters to scope
                for param in &func.params {
                    let ty = self.ast_to_type(&param.ty);
                    let symbol = Symbol::parameter(ty, param.span);
                    let _ = self.scopes.define(param.name.name.clone(), symbol);
                }

                self.check_block(&func.body);

                self.scopes.pop();
                self.current_return_type = None;
            }
            ItemKind::Const(c) => {
                let declared_ty = self.ast_to_type(&c.ty);
                let actual_ty = self.infer_expr_with_hint(&c.value, Some(&declared_ty));
                if !actual_ty.is_compatible_with(&declared_ty) {
                    self.error(
                        format!("constant '{}' has type {}, but initializer has type {}",
                            c.name.name, declared_ty, actual_ty),
                        c.value.span,
                    );
                }
            }
            ItemKind::Test(test) => {
                // Tests are like functions with no parameters and no return type
                self.current_return_type = Some(Type::unit());
                self.scopes.push();
                self.check_block(&test.body);
                self.scopes.pop();
                self.current_return_type = None;
            }
            ItemKind::Struct(_) | ItemKind::Layout(_) | ItemKind::Enum(_) => {
                // Type definitions don't need checking beyond parsing
            }
            ItemKind::Use(_) => {
                // Use statements are handled during loading
            }
        }
    }

    /// Check a block of statements
    fn check_block(&mut self, block: &parser::Block) {
        for stmt in &block.stmts {
            self.check_stmt(stmt);
        }
    }

    /// Check a statement
    fn check_stmt(&mut self, stmt: &parser::Stmt) {
        match &stmt.kind {
            parser::StmtKind::Let { name, ty, init, mutable } => {
                let declared_ty = ty.as_ref().map(|t| self.ast_to_type(t));

                if let Some(init) = init {
                    // Use declared type as hint for type inference
                    let init_ty = self.infer_expr_with_hint(init, declared_ty.as_ref());
                    if let Some(ref declared) = declared_ty {
                        if !init_ty.is_compatible_with(declared) {
                            self.error(
                                format!("cannot assign {} to variable of type {}", init_ty, declared),
                                init.span,
                            );
                        }
                    }
                }

                let var_ty = declared_ty.unwrap_or_else(|| {
                    if let Some(init) = init {
                        self.infer_expr(init)
                    } else {
                        self.error("variable without type annotation must have initializer", name.span);
                        Type::error()
                    }
                });

                let symbol = Symbol::variable(var_ty, name.span, *mutable);
                let _ = self.scopes.define(name.name.clone(), symbol);
            }
            parser::StmtKind::Expr(expr) => {
                self.infer_expr(expr);
            }
            parser::StmtKind::Assign { target, value } => {
                let target_ty = self.infer_expr(target);
                let value_ty = self.infer_expr(value);

                // Check assignability
                if !value_ty.is_compatible_with(&target_ty) {
                    self.error(
                        format!("cannot assign {} to {}", value_ty, target_ty),
                        value.span,
                    );
                }

                // Check that target is assignable (lvalue)
                self.check_assignable(target);
            }
            parser::StmtKind::CompoundAssign { target, op, value } => {
                let target_ty = self.infer_expr(target);
                let value_ty = self.infer_expr(value);

                // For compound assignment, both sides should be numeric
                if !target_ty.is_integer() || !value_ty.is_integer() {
                    self.error(
                        format!("compound assignment requires integer types, got {} and {}", target_ty, value_ty),
                        stmt.span,
                    );
                }

                self.check_assignable(target);
            }
            parser::StmtKind::If { condition, then_block, else_block } => {
                let cond_ty = self.infer_expr(condition);
                if !cond_ty.is_bool() && !cond_ty.is_error() {
                    self.error(
                        format!("if condition must be bool, got {}", cond_ty),
                        condition.span,
                    );
                }

                self.scopes.push();
                self.check_block(then_block);
                self.scopes.pop();

                if let Some(else_block) = else_block {
                    self.scopes.push();
                    self.check_block(else_block);
                    self.scopes.pop();
                }
            }
            parser::StmtKind::For { var, start, end, body, .. } => {
                let start_ty = self.infer_expr(start);
                let end_ty = self.infer_expr(end);

                if !start_ty.is_integer() && !start_ty.is_error() {
                    self.error(
                        format!("for loop start must be integer, got {}", start_ty),
                        start.span,
                    );
                }
                if !end_ty.is_integer() && !end_ty.is_error() {
                    self.error(
                        format!("for loop end must be integer, got {}", end_ty),
                        end.span,
                    );
                }

                self.scopes.push();
                // Loop variable has same type as range bounds (default to u64)
                let var_ty = if start_ty.is_integer() { start_ty } else { Type::int(64, false) };
                let symbol = Symbol::variable(var_ty, var.span, false);
                let _ = self.scopes.define(var.name.clone(), symbol);
                self.check_block(body);
                self.scopes.pop();
            }
            parser::StmtKind::While { condition, body } => {
                let cond_ty = self.infer_expr(condition);
                if !cond_ty.is_bool() && !cond_ty.is_error() {
                    self.error(
                        format!("while condition must be bool, got {}", cond_ty),
                        condition.span,
                    );
                }

                self.scopes.push();
                self.check_block(body);
                self.scopes.pop();
            }
            parser::StmtKind::Loop { body } => {
                self.scopes.push();
                self.check_block(body);
                self.scopes.pop();
            }
            parser::StmtKind::Break | parser::StmtKind::Continue => {
                // Could check if we're inside a loop, but that's a semantic check
            }
            parser::StmtKind::Return(expr) => {
                let return_ty = expr.as_ref()
                    .map(|e| self.infer_expr(e))
                    .unwrap_or_else(Type::unit);

                if let Some(ref expected) = self.current_return_type {
                    if !return_ty.is_compatible_with(expected) {
                        self.error(
                            format!("return type mismatch: expected {}, got {}", expected, return_ty),
                            stmt.span,
                        );
                    }
                }
            }
            parser::StmtKind::Block(block) => {
                self.scopes.push();
                self.check_block(block);
                self.scopes.pop();
            }
        }
    }

    /// Check that an expression is assignable (is an lvalue)
    fn check_assignable(&mut self, expr: &parser::Expr) {
        match &expr.kind {
            parser::ExprKind::Ident(ident) => {
                if let Some(sym) = self.scopes.lookup(&ident.name) {
                    if !sym.mutable && sym.kind == SymbolKind::Variable {
                        self.error(
                            format!("cannot assign to immutable variable '{}'", ident.name),
                            ident.span,
                        );
                    }
                }
            }
            parser::ExprKind::Index { array, .. } => {
                // Indexing into an array is assignable if the array is mutable
                self.check_assignable(array);
            }
            parser::ExprKind::Field { object, .. } => {
                // Field access is assignable if the object is mutable
                self.check_assignable(object);
            }
            parser::ExprKind::Deref(inner) => {
                // Dereferencing is assignable if inner is a mutable reference
                let inner_ty = self.infer_expr(inner);
                if !inner_ty.is_mut_ref() && !inner_ty.is_error() {
                    self.error("cannot assign through immutable reference", expr.span);
                }
            }
            parser::ExprKind::Cast { expr: inner, ty } => {
                // Cast is assignable if it's a slice-to-endian-int cast and inner is assignable
                // e.g., buf[0..4] as u32be = value;
                if let parser::TypeKind::Primitive(p) = &ty.kind {
                    let endian = p.endianness();
                    if endian != parser::Endianness::Native {
                        // Endian cast - check that inner is a slice expression
                        if let parser::ExprKind::Slice { array, .. } = &inner.kind {
                            self.check_assignable(array);
                            return;
                        }
                    }
                }
                self.error("cast expression is not assignable", expr.span);
            }
            parser::ExprKind::Slice { array, .. } => {
                // Slice is assignable if the underlying array is mutable
                self.check_assignable(array);
            }
            _ => {
                self.error("expression is not assignable", expr.span);
            }
        }
    }

    /// Infer the type of an expression with an optional expected type hint
    fn infer_expr_with_hint(&mut self, expr: &parser::Expr, hint: Option<&Type>) -> Type {
        // Handle array literals specially when we have a type hint
        if let parser::ExprKind::Array(elements) = &expr.kind {
            if let Some(expected) = hint {
                if let TypeKind::Array { element: expected_elem, size } = &expected.kind {
                    // Use the expected element type for each element
                    for elem in elements {
                        let elem_ty = self.infer_expr_with_hint(elem, Some(expected_elem));
                        if !elem_ty.is_compatible_with(expected_elem) {
                            self.error(
                                format!("array element type mismatch: expected {}, got {}", expected_elem, elem_ty),
                                elem.span,
                            );
                        }
                    }
                    if elements.len() as u64 != *size {
                        self.error(
                            format!("array length mismatch: expected {}, got {}", size, elements.len()),
                            expr.span,
                        );
                    }
                    return expected.clone();
                }
            }
        }

        // Handle array repeat syntax with type hint
        if let parser::ExprKind::ArrayRepeat { value, count } = &expr.kind {
            // Check that count is an integer type
            let count_ty = self.infer_expr(count);
            if !count_ty.is_integer() && !count_ty.is_error() {
                self.error(
                    format!("array repeat count must be integer, got {}", count_ty),
                    count.span,
                );
            }

            if let Some(expected) = hint {
                if let TypeKind::Array { element: expected_elem, size } = &expected.kind {
                    let elem_ty = self.infer_expr_with_hint(value, Some(expected_elem));
                    if !elem_ty.is_compatible_with(expected_elem) {
                        self.error(
                            format!("array element type mismatch: expected {}, got {}", expected_elem, elem_ty),
                            value.span,
                        );
                    }
                    // Only check size if count is a compile-time constant
                    if let parser::ExprKind::Integer(n) = &count.kind {
                        if *n as u64 != *size {
                            self.error(
                                format!("array length mismatch: expected {}, got {}", size, n),
                                expr.span,
                            );
                        }
                    }
                    return expected.clone();
                }
            }
        }

        // Handle integer literals with type hint
        if let parser::ExprKind::Integer(n) = &expr.kind {
            if let Some(expected) = hint {
                if let TypeKind::Int { bits, signed, .. } = &expected.kind {
                    // Check that the value fits in the expected type
                    let max_val = if *signed {
                        (1u128 << (bits - 1)) - 1
                    } else {
                        (1u128 << bits) - 1
                    };
                    if *n <= max_val {
                        return expected.clone();
                    }
                }
            }
        }

        // Fall back to regular inference
        self.infer_expr(expr)
    }

    /// Infer the type of an expression
    fn infer_expr(&mut self, expr: &parser::Expr) -> Type {
        match &expr.kind {
            parser::ExprKind::Integer(n) => {
                // Infer smallest type that fits
                if *n <= u8::MAX as u128 {
                    Type::int(8, false)
                } else if *n <= u16::MAX as u128 {
                    Type::int(16, false)
                } else if *n <= u32::MAX as u128 {
                    Type::int(32, false)
                } else if *n <= u64::MAX as u128 {
                    Type::int(64, false)
                } else {
                    Type::int(128, false)
                }
            }
            parser::ExprKind::Bool(_) => Type::bool(),
            parser::ExprKind::String(_) => {
                // Strings are slices of u8
                Type::slice(Type::int(8, false))
            }
            parser::ExprKind::Bytes(_) | parser::ExprKind::Hex(_) => {
                // bytes() and hex() return byte slices
                Type::slice(Type::int(8, false))
            }
            parser::ExprKind::Ident(ident) => {
                if let Some(sym) = self.scopes.lookup(&ident.name) {
                    sym.ty.clone()
                } else if let Some(sym) = self.global_scope.get(&ident.name) {
                    sym.ty.clone()
                } else {
                    self.error(format!("undefined variable '{}'", ident.name), ident.span);
                    Type::error()
                }
            }
            parser::ExprKind::Binary { left, op, right } => {
                // For binary ops, if one side is a literal and the other isn't,
                // infer the non-literal first and use it as a hint for the literal
                let left_is_literal = matches!(left.kind, parser::ExprKind::Integer(_));
                let right_is_literal = matches!(right.kind, parser::ExprKind::Integer(_));

                let (left_ty, right_ty) = if left_is_literal && !right_is_literal {
                    // Infer right first, use as hint for left
                    let right_ty = self.infer_expr(right);
                    let left_ty = self.infer_expr_with_hint(left, Some(&right_ty));
                    (left_ty, right_ty)
                } else if right_is_literal && !left_is_literal {
                    // Infer left first, use as hint for right
                    let left_ty = self.infer_expr(left);
                    let right_ty = self.infer_expr_with_hint(right, Some(&left_ty));
                    (left_ty, right_ty)
                } else {
                    // Both literals or neither - infer independently
                    (self.infer_expr(left), self.infer_expr(right))
                };

                self.check_binary_op(*op, &left_ty, &right_ty, expr.span)
            }
            parser::ExprKind::Unary { op, operand } => {
                let operand_ty = self.infer_expr(operand);
                self.check_unary_op(*op, &operand_ty, expr.span)
            }
            parser::ExprKind::Index { array, index } => {
                let array_ty = self.infer_expr(array);
                let index_ty = self.infer_expr(index);

                if !index_ty.is_integer() && !index_ty.is_error() {
                    self.error(
                        format!("index must be integer, got {}", index_ty),
                        index.span,
                    );
                }

                if let Some(elem_ty) = array_ty.element_type() {
                    elem_ty.clone()
                } else if !array_ty.is_error() {
                    self.error(
                        format!("cannot index into type {}", array_ty),
                        array.span,
                    );
                    Type::error()
                } else {
                    Type::error()
                }
            }
            parser::ExprKind::Slice { array, start, end, .. } => {
                let array_ty = self.infer_expr(array);
                let start_ty = self.infer_expr(start);
                let end_ty = self.infer_expr(end);

                if !start_ty.is_integer() && !start_ty.is_error() {
                    self.error(format!("slice start must be integer, got {}", start_ty), start.span);
                }
                if !end_ty.is_integer() && !end_ty.is_error() {
                    self.error(format!("slice end must be integer, got {}", end_ty), end.span);
                }

                if let Some(elem_ty) = array_ty.element_type() {
                    Type::slice(elem_ty.clone())
                } else if !array_ty.is_error() {
                    self.error(format!("cannot slice type {}", array_ty), array.span);
                    Type::error()
                } else {
                    Type::error()
                }
            }
            parser::ExprKind::Field { object, field } => {
                let object_ty = self.infer_expr(object);

                // Handle references
                let base_ty = if let Some(inner) = object_ty.deref_type() {
                    inner
                } else {
                    &object_ty
                };

                match &base_ty.kind {
                    TypeKind::Struct { name } => {
                        if let Some(struct_def) = self.global_scope.get_struct(name) {
                            if let Some(field_def) = struct_def.get_field(&field.name) {
                                field_def.ty.clone()
                            } else {
                                self.error(
                                    format!("struct '{}' has no field '{}'", name, field.name),
                                    field.span,
                                );
                                Type::error()
                            }
                        } else {
                            Type::error()
                        }
                    }
                    TypeKind::Error => Type::error(),
                    _ => {
                        self.error(
                            format!("cannot access field '{}' on type {}", field.name, object_ty),
                            field.span,
                        );
                        Type::error()
                    }
                }
            }
            parser::ExprKind::Call { func, args } => {
                // Check for Reader/Writer constructor calls
                if let parser::ExprKind::Ident(ident) = &func.kind {
                    if ident.name == "Reader" {
                        if args.len() != 1 {
                            self.error("Reader() requires exactly 1 argument (data)", expr.span);
                        } else {
                            let data_ty = self.infer_expr(&args[0]);
                            // Accept byte slices/arrays
                            if let Some(elem) = self.get_element_type(&data_ty) {
                                if !matches!(&elem.kind, TypeKind::Int { bits: 8, signed: false, .. }) {
                                    self.error(format!("Reader() data must be byte slice/array, got {}", data_ty), args[0].span);
                                }
                            } else if !data_ty.is_error() {
                                self.error(format!("Reader() data must be byte slice/array, got {}", data_ty), args[0].span);
                            }
                        }
                        return Type::reader();
                    }
                    if ident.name == "Writer" {
                        if args.len() != 1 {
                            self.error("Writer() requires exactly 1 argument (data)", expr.span);
                        } else {
                            let data_ty = self.infer_expr(&args[0]);
                            // Accept mutable byte slices/arrays
                            if let Some(elem) = self.get_element_type(&data_ty) {
                                if !matches!(&elem.kind, TypeKind::Int { bits: 8, signed: false, .. }) {
                                    self.error(format!("Writer() data must be byte slice/array, got {}", data_ty), args[0].span);
                                }
                            } else if !data_ty.is_error() {
                                self.error(format!("Writer() data must be byte slice/array, got {}", data_ty), args[0].span);
                            }
                        }
                        return Type::writer();
                    }
                }

                // Check for method calls (e.g., slice.len())
                if let parser::ExprKind::Field { object, field } = &func.kind {
                    let object_ty = self.infer_expr(object);
                    if let Some(result_ty) = self.check_method_call(&object_ty, &field.name, args, expr.span) {
                        return result_ty;
                    }
                }

                let func_ty = self.infer_expr(func);

                match &func_ty.kind {
                    TypeKind::Function { params, return_type } => {
                        if args.len() != params.len() {
                            self.error(
                                format!("expected {} arguments, got {}", params.len(), args.len()),
                                expr.span,
                            );
                        }

                        for (arg, param_ty) in args.iter().zip(params.iter()) {
                            let arg_ty = self.infer_expr(arg);
                            if !arg_ty.is_compatible_with(param_ty) {
                                self.error(
                                    format!("argument type mismatch: expected {}, got {}", param_ty, arg_ty),
                                    arg.span,
                                );
                            }
                        }

                        (**return_type).clone()
                    }
                    TypeKind::Error => Type::error(),
                    _ => {
                        self.error(format!("cannot call non-function type {}", func_ty), expr.span);
                        Type::error()
                    }
                }
            }
            parser::ExprKind::Builtin { name, args } => {
                self.check_builtin(*name, args, expr.span)
            }
            parser::ExprKind::Array(elements) => {
                if elements.is_empty() {
                    self.error("cannot infer type of empty array literal", expr.span);
                    return Type::error();
                }

                let elem_ty = self.infer_expr(&elements[0]);
                for elem in elements.iter().skip(1) {
                    let ty = self.infer_expr(elem);
                    if !ty.is_compatible_with(&elem_ty) {
                        self.error(
                            format!("array element type mismatch: expected {}, got {}", elem_ty, ty),
                            elem.span,
                        );
                    }
                }

                Type::array(elem_ty, elements.len() as u64)
            }
            parser::ExprKind::ArrayRepeat { value, count } => {
                let elem_ty = self.infer_expr(value);
                let count_ty = self.infer_expr(count);
                if !count_ty.is_integer() && !count_ty.is_error() {
                    self.error(
                        format!("array repeat count must be integer, got {}", count_ty),
                        count.span,
                    );
                }
                // If count is a constant, use it for the array size; otherwise use 0 (dynamic)
                let size = if let parser::ExprKind::Integer(n) = &count.kind {
                    *n as u64
                } else {
                    0 // Dynamic size - will be determined at runtime
                };
                Type::array(elem_ty, size)
            }
            parser::ExprKind::Cast { expr: inner, ty } => {
                let from_ty = self.infer_expr(inner);
                let to_ty = self.ast_to_type(ty);

                // Validate the cast
                self.check_cast(&from_ty, &to_ty, expr.span);

                to_ty
            }
            parser::ExprKind::Ref(inner) => {
                let inner_ty = self.infer_expr(inner);
                Type::reference(inner_ty, false)
            }
            parser::ExprKind::MutRef(inner) => {
                let inner_ty = self.infer_expr(inner);
                Type::reference(inner_ty, true)
            }
            parser::ExprKind::Deref(inner) => {
                let inner_ty = self.infer_expr(inner);
                if let Some(deref_ty) = inner_ty.deref_type() {
                    deref_ty.clone()
                } else if !inner_ty.is_error() {
                    self.error(format!("cannot dereference type {}", inner_ty), expr.span);
                    Type::error()
                } else {
                    Type::error()
                }
            }
            parser::ExprKind::Range { start, end, .. } => {
                let start_ty = self.infer_expr(start);
                let end_ty = self.infer_expr(end);
                if !start_ty.is_integer() && !start_ty.is_error() {
                    self.error(format!("range start must be integer, got {}", start_ty), start.span);
                }
                if !end_ty.is_integer() && !end_ty.is_error() {
                    self.error(format!("range end must be integer, got {}", end_ty), end.span);
                }
                // Range type - for now just return the start type
                start_ty
            }
            parser::ExprKind::Paren(inner) => self.infer_expr(inner),
            parser::ExprKind::StructLit { name, fields } => {
                if let Some(struct_def) = self.global_scope.get_struct(&name.name) {
                    // Check all required fields are provided
                    for field_def in &struct_def.fields {
                        if !fields.iter().any(|(n, _)| n.name == field_def.name) {
                            self.error(
                                format!("missing field '{}' in struct literal", field_def.name),
                                expr.span,
                            );
                        }
                    }

                    // Check provided fields
                    for (field_name, field_value) in fields {
                        if let Some(field_def) = struct_def.get_field(&field_name.name) {
                            let value_ty = self.infer_expr(field_value);
                            if !value_ty.is_compatible_with(&field_def.ty) {
                                self.error(
                                    format!("field '{}' expects {}, got {}",
                                        field_name.name, field_def.ty, value_ty),
                                    field_value.span,
                                );
                            }
                        } else {
                            self.error(
                                format!("struct '{}' has no field '{}'", name.name, field_name.name),
                                field_name.span,
                            );
                        }
                    }

                    Type::struct_type(name.name.clone())
                } else {
                    Type::error()
                }
            }
            parser::ExprKind::Conditional { condition, then_expr, else_expr } => {
                // Check condition is boolean
                let cond_ty = self.infer_expr(condition);
                if !cond_ty.is_bool() && !cond_ty.is_error() {
                    self.error(
                        format!("conditional expression requires bool condition, got {}", cond_ty),
                        condition.span,
                    );
                }

                // Check both branches and ensure they have compatible types
                let then_ty = self.infer_expr(then_expr);
                let else_ty = self.infer_expr(else_expr);

                if then_ty.is_error() {
                    return else_ty;
                }
                if else_ty.is_error() {
                    return then_ty;
                }

                if !then_ty.is_compatible_with(&else_ty) {
                    self.error(
                        format!("conditional branches have incompatible types: {} and {}",
                            then_ty, else_ty),
                        expr.span,
                    );
                    return Type::error();
                }

                // Return the more specific type (or either if they're the same)
                then_ty
            }
            parser::ExprKind::EnumVariant { enum_name, variant_name: _, args: _ } => {
                // For now, return the enum type
                // TODO: Validate variant exists and args match
                Type::new(TypeKind::Enum { name: enum_name.name.clone() })
            }
            parser::ExprKind::Match { expr: match_expr, arms } => {
                // Infer the type of the matched expression
                let _match_ty = self.infer_expr(match_expr);

                // Infer types of all arm bodies and ensure they're compatible
                let mut result_ty: Option<Type> = None;
                for arm in arms {
                    // TODO: Check pattern against match_ty
                    let arm_ty = self.infer_expr(&arm.body);
                    if arm_ty.is_error() {
                        continue;
                    }
                    if let Some(ref expected) = result_ty {
                        if !arm_ty.is_compatible_with(expected) {
                            self.error(
                                format!("match arm has incompatible type: expected {}, got {}", expected, arm_ty),
                                arm.span,
                            );
                        }
                    } else {
                        result_ty = Some(arm_ty);
                    }
                }
                result_ty.unwrap_or_else(Type::error)
            }
        }
    }

    /// Check binary operator types
    fn check_binary_op(&mut self, op: BinaryOp, left: &Type, right: &Type, span: SourceSpan) -> Type {
        if left.is_error() || right.is_error() {
            return Type::error();
        }

        match op {
            // Arithmetic operators: integer -> integer
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem => {
                if !left.is_integer() || !right.is_integer() {
                    self.error(
                        format!("arithmetic operator requires integer operands, got {} and {}", left, right),
                        span,
                    );
                    return Type::error();
                }
                // Result type is the larger of the two
                if left.bit_width() >= right.bit_width() {
                    left.clone()
                } else {
                    right.clone()
                }
            }
            // Bitwise operators: integer -> integer
            BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor => {
                if !left.is_integer() || !right.is_integer() {
                    self.error(
                        format!("bitwise operator requires integer operands, got {} and {}", left, right),
                        span,
                    );
                    return Type::error();
                }
                if left.bit_width() >= right.bit_width() {
                    left.clone()
                } else {
                    right.clone()
                }
            }
            // Shift operators: integer, integer -> integer
            BinaryOp::Shl | BinaryOp::Shr => {
                if !left.is_integer() || !right.is_integer() {
                    self.error(
                        format!("shift operator requires integer operands, got {} and {}", left, right),
                        span,
                    );
                    return Type::error();
                }
                left.clone()
            }
            // Comparison operators: comparable -> bool
            BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                if !left.is_compatible_with(right) {
                    self.error(
                        format!("cannot compare {} and {}", left, right),
                        span,
                    );
                }
                Type::bool()
            }
            // Logical operators: bool, bool -> bool
            BinaryOp::And | BinaryOp::Or => {
                if !left.is_bool() || !right.is_bool() {
                    self.error(
                        format!("logical operator requires boolean operands, got {} and {}", left, right),
                        span,
                    );
                    return Type::error();
                }
                Type::bool()
            }
        }
    }

    /// Check unary operator types
    fn check_unary_op(&mut self, op: UnaryOp, operand: &Type, span: SourceSpan) -> Type {
        if operand.is_error() {
            return Type::error();
        }

        match op {
            UnaryOp::Neg => {
                if !operand.is_integer() {
                    self.error(format!("negation requires integer, got {}", operand), span);
                    return Type::error();
                }
                operand.clone()
            }
            UnaryOp::Not => {
                if !operand.is_bool() {
                    self.error(format!("logical not requires bool, got {}", operand), span);
                    return Type::error();
                }
                Type::bool()
            }
            UnaryOp::BitNot => {
                if !operand.is_integer() {
                    self.error(format!("bitwise not requires integer, got {}", operand), span);
                    return Type::error();
                }
                operand.clone()
            }
        }
    }

    /// Check builtin function types
    fn check_builtin(&mut self, name: BuiltinFunc, args: &[parser::Expr], span: SourceSpan) -> Type {
        match name {
            BuiltinFunc::Assert => {
                if args.len() != 1 {
                    self.error(format!("assert requires 1 argument, got {}", args.len()), span);
                    return Type::error();
                }
                let cond_ty = self.infer_expr(&args[0]);
                if !cond_ty.is_bool() && !cond_ty.is_error() {
                    self.error(format!("assert condition must be bool, got {}", cond_ty), args[0].span);
                }
                Type::unit()
            }
        }
    }

    #[allow(dead_code)]
    fn check_read_args(&mut self, args: &[parser::Expr], bits: u32, span: SourceSpan) -> Type {
        if args.len() != 2 {
            self.error(format!("read function requires 2 arguments (buffer, offset), got {}", args.len()), span);
            return Type::error();
        }
        let buf_ty = self.infer_expr(&args[0]);
        let offset_ty = self.infer_expr(&args[1]);

        // Buffer should be a reference to bytes
        if !buf_ty.is_ref() && !buf_ty.is_error() {
            self.error(format!("read buffer must be a reference, got {}", buf_ty), args[0].span);
        }
        if !offset_ty.is_integer() && !offset_ty.is_error() {
            self.error(format!("offset must be integer, got {}", offset_ty), args[1].span);
        }

        Type::int(bits, false)
    }

    fn check_write_args(&mut self, args: &[parser::Expr], bits: u32, span: SourceSpan) {
        if args.len() != 3 {
            self.error(format!("write function requires 3 arguments (buffer, offset, value), got {}", args.len()), span);
            return;
        }
        let buf_ty = self.infer_expr(&args[0]);
        let offset_ty = self.infer_expr(&args[1]);
        let value_ty = self.infer_expr(&args[2]);

        if !buf_ty.is_mut_ref() && !buf_ty.is_error() {
            self.error(format!("write buffer must be a mutable reference, got {}", buf_ty), args[0].span);
        }
        if !offset_ty.is_integer() && !offset_ty.is_error() {
            self.error(format!("offset must be integer, got {}", offset_ty), args[1].span);
        }
        if !value_ty.is_integer() && !value_ty.is_error() {
            self.error(format!("value must be integer, got {}", value_ty), args[2].span);
        }
    }

    /// Check method call on a type (e.g., slice.len())
    /// Returns Some(result_type) if it's a valid method call, None if not a method
    fn check_method_call(&mut self, object_ty: &Type, method: &str, args: &[parser::Expr], span: SourceSpan) -> Option<Type> {
        // Handle references by dereferencing
        let base_ty = if let Some(inner) = object_ty.deref_type() {
            inner
        } else {
            object_ty
        };

        // Check for Reader methods
        if base_ty.is_reader() {
            return self.check_reader_method(method, args, span);
        }

        // Check for Writer methods
        if base_ty.is_writer() {
            return self.check_writer_method(method, args, span);
        }

        match method {
            "len" => {
                // .len() is valid on arrays and slices
                match &base_ty.kind {
                    TypeKind::Array { .. } | TypeKind::Slice { .. } => {
                        if !args.is_empty() {
                            self.error("len() takes no arguments", span);
                        }
                        Some(Type::int(64, false)) // u64
                    }
                    _ => None,
                }
            }
            _ => None, // Not a known method
        }
    }

    /// Check Reader method calls
    fn check_reader_method(&mut self, method: &str, args: &[parser::Expr], span: SourceSpan) -> Option<Type> {
        match method {
            // Single-byte read (no endianness)
            "read_u8" => {
                if !args.is_empty() {
                    self.error("read_u8() takes no arguments", span);
                }
                Some(Type::int(8, false))
            }
            // Native endian reads (default to big-endian behavior)
            "read_u16" | "read_u16be" => {
                if !args.is_empty() {
                    self.error(format!("{}() takes no arguments", method), span);
                }
                Some(Type::int(16, false))
            }
            "read_u16le" => {
                if !args.is_empty() {
                    self.error("read_u16le() takes no arguments", span);
                }
                Some(Type::int(16, false))
            }
            "read_u32" | "read_u32be" => {
                if !args.is_empty() {
                    self.error(format!("{}() takes no arguments", method), span);
                }
                Some(Type::int(32, false))
            }
            "read_u32le" => {
                if !args.is_empty() {
                    self.error("read_u32le() takes no arguments", span);
                }
                Some(Type::int(32, false))
            }
            "read_u64" | "read_u64be" => {
                if !args.is_empty() {
                    self.error(format!("{}() takes no arguments", method), span);
                }
                Some(Type::int(64, false))
            }
            "read_u64le" => {
                if !args.is_empty() {
                    self.error("read_u64le() takes no arguments", span);
                }
                Some(Type::int(64, false))
            }
            // Exact-count byte read (fails if not enough bytes)
            "read_bytes" => {
                if args.len() != 1 {
                    self.error("read_bytes() requires exactly 1 argument (count)", span);
                } else {
                    let count_ty = self.infer_expr(&args[0]);
                    if !count_ty.is_integer() && !count_ty.is_error() {
                        self.error(format!("read_bytes() count must be integer, got {}", count_ty), args[0].span);
                    }
                }
                Some(Type::slice(Type::int(8, false))) // &[u8]
            }
            // Chunk read (returns up to max bytes, empty at EOF)
            "read_chunk" => {
                if args.len() != 1 {
                    self.error("read_chunk() requires exactly 1 argument (max_size)", span);
                } else {
                    let max_ty = self.infer_expr(&args[0]);
                    if !max_ty.is_integer() && !max_ty.is_error() {
                        self.error(format!("read_chunk() max_size must be integer, got {}", max_ty), args[0].span);
                    }
                }
                Some(Type::slice(Type::int(8, false))) // &[u8]
            }
            // EOF check
            "eof" => {
                if !args.is_empty() {
                    self.error("eof() takes no arguments", span);
                }
                Some(Type::bool())
            }
            _ => {
                self.error(format!("Reader has no method '{}'", method), span);
                Some(Type::error())
            }
        }
    }

    /// Check Writer method calls
    fn check_writer_method(&mut self, method: &str, args: &[parser::Expr], span: SourceSpan) -> Option<Type> {
        match method {
            // Single-byte write
            "write_u8" => {
                if args.len() != 1 {
                    self.error("write_u8() requires exactly 1 argument", span);
                } else {
                    let val_ty = self.infer_expr(&args[0]);
                    if !val_ty.is_integer() && !val_ty.is_error() {
                        self.error(format!("write_u8() value must be integer, got {}", val_ty), args[0].span);
                    }
                }
                Some(Type::unit())
            }
            // Native endian writes (default to big-endian behavior)
            "write_u16" | "write_u16be" => {
                if args.len() != 1 {
                    self.error(format!("{}() requires exactly 1 argument", method), span);
                } else {
                    let val_ty = self.infer_expr(&args[0]);
                    if !val_ty.is_integer() && !val_ty.is_error() {
                        self.error(format!("{}() value must be integer, got {}", method, val_ty), args[0].span);
                    }
                }
                Some(Type::unit())
            }
            "write_u16le" => {
                if args.len() != 1 {
                    self.error("write_u16le() requires exactly 1 argument", span);
                } else {
                    let val_ty = self.infer_expr(&args[0]);
                    if !val_ty.is_integer() && !val_ty.is_error() {
                        self.error(format!("write_u16le() value must be integer, got {}", val_ty), args[0].span);
                    }
                }
                Some(Type::unit())
            }
            "write_u32" | "write_u32be" => {
                if args.len() != 1 {
                    self.error(format!("{}() requires exactly 1 argument", method), span);
                } else {
                    let val_ty = self.infer_expr(&args[0]);
                    if !val_ty.is_integer() && !val_ty.is_error() {
                        self.error(format!("{}() value must be integer, got {}", method, val_ty), args[0].span);
                    }
                }
                Some(Type::unit())
            }
            "write_u32le" => {
                if args.len() != 1 {
                    self.error("write_u32le() requires exactly 1 argument", span);
                } else {
                    let val_ty = self.infer_expr(&args[0]);
                    if !val_ty.is_integer() && !val_ty.is_error() {
                        self.error(format!("write_u32le() value must be integer, got {}", val_ty), args[0].span);
                    }
                }
                Some(Type::unit())
            }
            "write_u64" | "write_u64be" => {
                if args.len() != 1 {
                    self.error(format!("{}() requires exactly 1 argument", method), span);
                } else {
                    let val_ty = self.infer_expr(&args[0]);
                    if !val_ty.is_integer() && !val_ty.is_error() {
                        self.error(format!("{}() value must be integer, got {}", method, val_ty), args[0].span);
                    }
                }
                Some(Type::unit())
            }
            "write_u64le" => {
                if args.len() != 1 {
                    self.error("write_u64le() requires exactly 1 argument", span);
                } else {
                    let val_ty = self.infer_expr(&args[0]);
                    if !val_ty.is_integer() && !val_ty.is_error() {
                        self.error(format!("write_u64le() value must be integer, got {}", val_ty), args[0].span);
                    }
                }
                Some(Type::unit())
            }
            // Byte slice write
            "write_bytes" => {
                if args.len() != 1 {
                    self.error("write_bytes() requires exactly 1 argument (data)", span);
                } else {
                    let data_ty = self.infer_expr(&args[0]);
                    // Check it's a byte slice or array
                    let elem_ty = self.get_element_type(&data_ty);
                    if let Some(elem) = elem_ty {
                        if !matches!(&elem.kind, TypeKind::Int { bits: 8, signed: false, .. }) {
                            self.error(format!("write_bytes() data must be byte slice/array, got {}", data_ty), args[0].span);
                        }
                    } else if !data_ty.is_error() {
                        self.error(format!("write_bytes() data must be byte slice/array, got {}", data_ty), args[0].span);
                    }
                }
                Some(Type::unit())
            }
            _ => {
                self.error(format!("Writer has no method '{}'", method), span);
                Some(Type::error())
            }
        }
    }

    /// Check if a cast is valid
    fn check_cast(&mut self, from_ty: &Type, to_ty: &Type, span: SourceSpan) {
        if from_ty.is_error() || to_ty.is_error() {
            return; // Skip checking if there's already an error
        }

        // Integer to integer casts are always allowed (including endianness changes)
        if from_ty.is_integer() && to_ty.is_integer() {
            return;
        }

        // Bool to integer and integer to bool
        if (from_ty.is_bool() && to_ty.is_integer()) || (from_ty.is_integer() && to_ty.is_bool()) {
            return;
        }

        // Slice/array of u8 to integer type (byte reinterpretation)
        // e.g., buf[0..4] as u32be
        if to_ty.is_integer() {
            let elem_ty = self.get_element_type(from_ty);
            if let Some(elem) = elem_ty {
                // Check element is u8
                if let TypeKind::Int { bits: 8, signed: false, .. } = &elem.kind {
                    // Valid: byte slice/array to integer
                    // The size check is done at runtime (slice) or could be checked
                    // at compile time for fixed-size arrays
                    if let TypeKind::Array { size, .. } = &from_ty.kind {
                        let required_bytes = to_ty.bit_width().unwrap_or(0) / 8;
                        if *size != required_bytes as u64 {
                            self.error(
                                format!("cannot cast [u8; {}] to {}: expected {} bytes",
                                    size, to_ty, required_bytes),
                                span,
                            );
                        }
                    }
                    // For slices, size is checked at runtime
                    return;
                }
            }
        }

        // Integer to byte array (for writing endian values)
        // e.g., value as u8[4] - this produces bytes in the integer's endian format
        if from_ty.is_integer() {
            if let TypeKind::Array { element, size } = &to_ty.kind {
                if let TypeKind::Int { bits: 8, signed: false, .. } = &element.kind {
                    let from_bytes = from_ty.bit_width().unwrap_or(0) / 8;
                    if *size == from_bytes as u64 {
                        return; // Valid: integer to byte array
                    } else {
                        self.error(
                            format!("cannot cast {} to [u8; {}]: {} has {} bytes",
                                from_ty, size, from_ty, from_bytes),
                            span,
                        );
                        return;
                    }
                }
            }
        }

        // Reference casts (strip mutability, etc.)
        if from_ty.is_ref() && to_ty.is_ref() {
            // Check inner types are compatible
            if let (Some(from_inner), Some(to_inner)) = (from_ty.deref_type(), to_ty.deref_type()) {
                if from_inner.is_compatible_with(to_inner) {
                    return;
                }
            }
        }

        // If none of the above, it's an invalid cast
        self.error(
            format!("cannot cast {} to {}", from_ty, to_ty),
            span,
        );
    }

    /// Helper to get element type from array, slice, or reference to array/slice
    fn get_element_type<'b>(&self, ty: &'b Type) -> Option<&'b Type> {
        match &ty.kind {
            TypeKind::Array { element, .. } => Some(element),
            TypeKind::Slice { element } => Some(element),
            TypeKind::Ref { inner, .. } => self.get_element_type(inner),
            _ => None,
        }
    }
}
