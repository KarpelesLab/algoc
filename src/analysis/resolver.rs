//! Name resolution pass
//!
//! Resolves all names to their definitions and builds symbol tables.

use crate::errors::{AlgocError, AlgocResult, SourceSpan};
use crate::parser::{self, Ast, Item, ItemKind, PrimitiveType as AstPrimitive};
use super::scope::{Scope, ScopeStack, Symbol, StructDef, StructField, EnumDef, EnumVariantDef};
use super::types::{Type, TypeKind, Endianness};

/// Name resolver that builds symbol tables
pub struct Resolver {
    /// The scope stack
    scopes: ScopeStack,
    /// Collected errors (we continue after errors for better diagnostics)
    errors: Vec<AlgocError>,
}

impl Resolver {
    /// Create a new resolver
    pub fn new() -> Self {
        Self {
            scopes: ScopeStack::new(),
            errors: Vec::new(),
        }
    }

    /// Resolve names in the AST and return the global scope
    pub fn resolve(mut self, ast: &Ast) -> AlgocResult<Scope> {
        // First pass: collect all top-level declarations (structs, functions, constants)
        for item in &ast.items {
            self.declare_item(item);
        }

        // Second pass: resolve bodies
        for item in &ast.items {
            self.resolve_item(item);
        }

        if !self.errors.is_empty() {
            return Err(self.errors.remove(0));
        }

        Ok(self.scopes.into_global())
    }

    /// Record an error
    fn error(&mut self, message: impl Into<String>, span: SourceSpan) {
        self.errors.push(AlgocError::semantic(message, span));
    }

    /// Convert an AST type to a resolved type
    fn resolve_type(&mut self, ty: &parser::Type) -> Type {
        match &ty.kind {
            parser::TypeKind::Primitive(p) => self.primitive_to_type(*p),
            parser::TypeKind::Array { element, size } => {
                let elem_ty = self.resolve_type(element);
                Type::array(elem_ty, *size)
            }
            parser::TypeKind::Slice { element } => {
                let elem_ty = self.resolve_type(element);
                Type::slice(elem_ty)
            }
            parser::TypeKind::ArrayRef { element, size } => {
                let elem_ty = self.resolve_type(element);
                Type::reference(Type::array(elem_ty, *size), false)
            }
            parser::TypeKind::MutRef(inner) => {
                let inner_ty = self.resolve_type(inner);
                Type::reference(inner_ty, true)
            }
            parser::TypeKind::Ref(inner) => {
                let inner_ty = self.resolve_type(inner);
                Type::reference(inner_ty, false)
            }
            parser::TypeKind::Named(ident) => {
                // Check for built-in Reader/Writer types
                match ident.name.as_str() {
                    "Reader" => Type::reader(),
                    "Writer" => Type::writer(),
                    _ => {
                        // Check if it's a known struct
                        if self.scopes.lookup_struct(&ident.name).is_some() {
                            Type::struct_type(ident.name.clone())
                        // Check if it's a known enum
                        } else if self.scopes.lookup_enum(&ident.name).is_some() {
                            Type::new(TypeKind::Enum { name: ident.name.clone() })
                        } else {
                            self.error(format!("unknown type '{}'", ident.name), ident.span);
                            Type::error()
                        }
                    }
                }
            }
        }
    }

    /// Convert an AST primitive type to a resolved type
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

    /// Declare a top-level item (first pass)
    fn declare_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => {
                // Build function type
                let params: Vec<Type> = func.params.iter()
                    .map(|p| self.resolve_type(&p.ty))
                    .collect();
                let return_type = func.return_type.as_ref()
                    .map(|t| self.resolve_type(t))
                    .unwrap_or_else(Type::unit);

                let func_type = Type::new(TypeKind::Function {
                    params,
                    return_type: Box::new(return_type),
                });

                let symbol = Symbol::function(func_type, func.name.span);
                if let Err(e) = self.scopes.global_mut().define(func.name.name.clone(), symbol) {
                    self.error(e, func.name.span);
                }
            }
            ItemKind::Struct(s) => {
                let mut def = StructDef::new(s.name.name.clone(), s.name.span);
                for field in &s.fields {
                    let field_ty = self.resolve_type(&field.ty);
                    def.add_field(StructField::new(
                        field.name.name.clone(),
                        field_ty,
                        field.span,
                    ));
                }
                if let Err(e) = self.scopes.global_mut().define_struct(s.name.name.clone(), def) {
                    self.error(e, s.name.span);
                }
            }
            ItemKind::Layout(l) => {
                // Layouts are similar to structs for type purposes
                let mut def = StructDef::new(l.name.name.clone(), l.name.span);
                for field in &l.fields {
                    let field_ty = self.resolve_type(&field.ty);
                    def.add_field(StructField::new(
                        field.name.name.clone(),
                        field_ty,
                        field.span,
                    ));
                }
                if let Err(e) = self.scopes.global_mut().define_struct(l.name.name.clone(), def) {
                    self.error(e, l.name.span);
                }
            }
            ItemKind::Const(c) => {
                let ty = self.resolve_type(&c.ty);
                let symbol = Symbol::constant(ty, c.name.span);
                if let Err(e) = self.scopes.global_mut().define(c.name.name.clone(), symbol) {
                    self.error(e, c.name.span);
                }
            }
            ItemKind::Test(_) => {
                // Tests don't declare symbols
            }
            ItemKind::Use(_) => {
                // Use statements are handled during loading, not here
            }
            ItemKind::Enum(e) => {
                // Register enum definition
                let mut def = EnumDef::new(e.name.name.clone(), e.name.span);
                for variant in &e.variants {
                    let data_types: Vec<Type> = match &variant.data {
                        parser::EnumVariantData::Unit => Vec::new(),
                        parser::EnumVariantData::Tuple(types) => {
                            types.iter().map(|t| self.resolve_type(t)).collect()
                        }
                        parser::EnumVariantData::Struct(fields) => {
                            fields.iter().map(|f| self.resolve_type(&f.ty)).collect()
                        }
                    };
                    def.add_variant(EnumVariantDef::new(
                        variant.name.name.clone(),
                        data_types,
                        variant.span,
                    ));
                }
                if let Err(err) = self.scopes.global_mut().define_enum(e.name.name.clone(), def) {
                    self.error(err, e.name.span);
                }

                // Also define the enum as a symbol for use in expressions
                let enum_type = Type::new(TypeKind::Enum { name: e.name.name.clone() });
                let symbol = Symbol::constant(enum_type, e.name.span);
                if let Err(err) = self.scopes.global_mut().define(e.name.name.clone(), symbol) {
                    self.error(err, e.name.span);
                }
            }
            ItemKind::Impl(impl_def) => {
                // Check that the target struct exists
                if self.scopes.lookup_struct(&impl_def.target.name).is_none() {
                    self.error(format!("impl for unknown type '{}'", impl_def.target.name), impl_def.target.span);
                    return;
                }

                // Register each method with a mangled name: StructName__method_name
                for method in &impl_def.methods {
                    // Build method type (includes self parameter)
                    let params: Vec<Type> = method.params.iter()
                        .map(|p| self.resolve_type(&p.ty))
                        .collect();
                    let return_type = method.return_type.as_ref()
                        .map(|t| self.resolve_type(t))
                        .unwrap_or_else(Type::unit);

                    let func_type = Type::new(TypeKind::Function {
                        params,
                        return_type: Box::new(return_type),
                    });

                    // Register as StructName__method
                    let mangled_name = format!("{}__{}",impl_def.target.name, method.name.name);
                    let symbol = Symbol::function(func_type, method.name.span);
                    if let Err(e) = self.scopes.global_mut().define(mangled_name.clone(), symbol) {
                        self.error(e, method.name.span);
                    }

                    // Also register the method in the struct's method table
                    if let Some(struct_def) = self.scopes.global_mut().get_struct_mut(&impl_def.target.name) {
                        struct_def.add_method(method.name.name.clone(), mangled_name);
                    }
                }
            }
        }
    }

    /// Resolve an item's body (second pass)
    fn resolve_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => {
                self.scopes.push();

                // Add parameters to scope
                for param in &func.params {
                    let ty = self.resolve_type(&param.ty);
                    // Check if parameter is mutable reference
                    let mutable = matches!(ty.kind, TypeKind::Ref { mutable: true, .. });
                    let symbol = Symbol::parameter(ty, param.span);
                    if let Err(e) = self.scopes.define(param.name.name.clone(), symbol) {
                        self.error(e, param.name.span);
                    }
                }

                // Resolve function body
                self.resolve_block(&func.body);

                self.scopes.pop();
            }
            ItemKind::Const(c) => {
                // Resolve the constant's initializer expression
                self.resolve_expr(&c.value);
            }
            ItemKind::Test(t) => {
                // Tests are like functions - resolve their body
                self.scopes.push();
                self.resolve_block(&t.body);
                self.scopes.pop();
            }
            ItemKind::Struct(_) | ItemKind::Layout(_) | ItemKind::Enum(_) => {
                // Already handled in declare_item
            }
            ItemKind::Use(_) => {
                // Use statements are handled during loading
            }
            ItemKind::Impl(impl_def) => {
                // Resolve each method's body
                for method in &impl_def.methods {
                    self.scopes.push();

                    // Add parameters to scope
                    for param in &method.params {
                        let ty = self.resolve_type(&param.ty);
                        let symbol = Symbol::parameter(ty, param.span);
                        if let Err(e) = self.scopes.define(param.name.name.clone(), symbol) {
                            self.error(e, param.name.span);
                        }
                    }

                    // Resolve method body
                    self.resolve_block(&method.body);

                    self.scopes.pop();
                }
            }
        }
    }

    /// Resolve a block
    fn resolve_block(&mut self, block: &parser::Block) {
        for stmt in &block.stmts {
            self.resolve_stmt(stmt);
        }
    }

    /// Resolve a statement
    fn resolve_stmt(&mut self, stmt: &parser::Stmt) {
        match &stmt.kind {
            parser::StmtKind::Let { name, ty, mutable, init } => {
                // Resolve the type if specified
                let var_ty = ty.as_ref()
                    .map(|t| self.resolve_type(t))
                    .unwrap_or_else(Type::error);

                // Resolve the initializer if present
                if let Some(init) = init {
                    self.resolve_expr(init);
                }

                // Add variable to scope
                let symbol = Symbol::variable(var_ty, name.span, *mutable);
                if let Err(e) = self.scopes.define(name.name.clone(), symbol) {
                    self.error(e, name.span);
                }
            }
            parser::StmtKind::Expr(expr) => {
                self.resolve_expr(expr);
            }
            parser::StmtKind::Assign { target, value } => {
                self.resolve_expr(target);
                self.resolve_expr(value);
            }
            parser::StmtKind::CompoundAssign { target, value, .. } => {
                self.resolve_expr(target);
                self.resolve_expr(value);
            }
            parser::StmtKind::If { condition, then_block, else_block } => {
                self.resolve_expr(condition);
                self.scopes.push();
                self.resolve_block(then_block);
                self.scopes.pop();
                if let Some(else_block) = else_block {
                    self.scopes.push();
                    self.resolve_block(else_block);
                    self.scopes.pop();
                }
            }
            parser::StmtKind::For { var, start, end, body, .. } => {
                self.resolve_expr(start);
                self.resolve_expr(end);

                self.scopes.push();
                // Add loop variable to scope (infer type as the same as start/end for now)
                let symbol = Symbol::variable(Type::int(64, false), var.span, false);
                if let Err(e) = self.scopes.define(var.name.clone(), symbol) {
                    self.error(e, var.span);
                }
                self.resolve_block(body);
                self.scopes.pop();
            }
            parser::StmtKind::While { condition, body } => {
                self.resolve_expr(condition);
                self.scopes.push();
                self.resolve_block(body);
                self.scopes.pop();
            }
            parser::StmtKind::Loop { body } => {
                self.scopes.push();
                self.resolve_block(body);
                self.scopes.pop();
            }
            parser::StmtKind::Break | parser::StmtKind::Continue => {
                // Nothing to resolve
            }
            parser::StmtKind::Return(expr) => {
                if let Some(expr) = expr {
                    self.resolve_expr(expr);
                }
            }
            parser::StmtKind::Block(block) => {
                self.scopes.push();
                self.resolve_block(block);
                self.scopes.pop();
            }
        }
    }

    /// Resolve an expression
    fn resolve_expr(&mut self, expr: &parser::Expr) {
        match &expr.kind {
            parser::ExprKind::Integer(_) |
            parser::ExprKind::Bool(_) |
            parser::ExprKind::String(_) |
            parser::ExprKind::Bytes(_) |
            parser::ExprKind::Hex(_) => {
                // Literals don't need resolution
            }
            parser::ExprKind::Ident(ident) => {
                // Reader and Writer are built-in type constructors, not variables
                if ident.name != "Reader" && ident.name != "Writer" {
                    if self.scopes.lookup(&ident.name).is_none() {
                        self.error(format!("undefined variable '{}'", ident.name), ident.span);
                    }
                }
            }
            parser::ExprKind::Binary { left, right, .. } => {
                self.resolve_expr(left);
                self.resolve_expr(right);
            }
            parser::ExprKind::Unary { operand, .. } => {
                self.resolve_expr(operand);
            }
            parser::ExprKind::Index { array, index } => {
                self.resolve_expr(array);
                self.resolve_expr(index);
            }
            parser::ExprKind::Slice { array, start, end, .. } => {
                self.resolve_expr(array);
                self.resolve_expr(start);
                self.resolve_expr(end);
            }
            parser::ExprKind::Field { object, field } => {
                self.resolve_expr(object);
                // Field resolution needs type information, done in type checker
                let _ = field; // Will be checked later
            }
            parser::ExprKind::Call { func, args } => {
                self.resolve_expr(func);
                for arg in args {
                    self.resolve_expr(arg);
                }
            }
            parser::ExprKind::Builtin { args, .. } => {
                for arg in args {
                    self.resolve_expr(arg);
                }
            }
            parser::ExprKind::Array(elements) => {
                for elem in elements {
                    self.resolve_expr(elem);
                }
            }
            parser::ExprKind::ArrayRepeat { value, count } => {
                self.resolve_expr(value);
                self.resolve_expr(count);
            }
            parser::ExprKind::Cast { expr, ty } => {
                self.resolve_expr(expr);
                self.resolve_type(ty);
            }
            parser::ExprKind::Ref(inner) |
            parser::ExprKind::MutRef(inner) |
            parser::ExprKind::Deref(inner) |
            parser::ExprKind::Paren(inner) => {
                self.resolve_expr(inner);
            }
            parser::ExprKind::Range { start, end, .. } => {
                self.resolve_expr(start);
                self.resolve_expr(end);
            }
            parser::ExprKind::StructLit { name, fields } => {
                // Check struct exists
                if self.scopes.lookup_struct(&name.name).is_none() {
                    self.error(format!("unknown struct '{}'", name.name), name.span);
                }
                for (_, value) in fields {
                    self.resolve_expr(value);
                }
            }
            parser::ExprKind::Conditional { condition, then_expr, else_expr } => {
                self.resolve_expr(condition);
                self.resolve_expr(then_expr);
                self.resolve_expr(else_expr);
            }
            parser::ExprKind::EnumVariant { enum_name, variant_name: _, args } => {
                // Check enum exists - for now just check if the name is defined
                if self.scopes.lookup(&enum_name.name).is_none() {
                    self.error(format!("unknown enum '{}'", enum_name.name), enum_name.span);
                }
                for arg in args {
                    self.resolve_expr(arg);
                }
            }
            parser::ExprKind::Match { expr, arms } => {
                self.resolve_expr(expr);
                for arm in arms {
                    // Resolve pattern bindings and arm body
                    self.scopes.push();
                    self.resolve_pattern(&arm.pattern);
                    self.resolve_expr(&arm.body);
                    self.scopes.pop();
                }
            }
            parser::ExprKind::MethodCall { receiver, args, .. } => {
                // Resolve receiver and arguments
                self.resolve_expr(receiver);
                for arg in args {
                    self.resolve_expr(arg);
                }
            }
        }
    }

    /// Resolve a pattern (for match arms)
    fn resolve_pattern(&mut self, pattern: &parser::Pattern) {
        match &pattern.kind {
            parser::PatternKind::Wildcard => {}
            parser::PatternKind::Literal(expr) => {
                self.resolve_expr(expr);
            }
            parser::PatternKind::Ident(ident) => {
                // Pattern identifiers introduce new bindings
                // Type will be inferred during type checking
                let symbol = Symbol::variable(Type::new(TypeKind::Error), ident.span, false);
                if let Err(e) = self.scopes.current_mut().define(ident.name.clone(), symbol) {
                    self.error(e, ident.span);
                }
            }
            parser::PatternKind::EnumVariant { enum_name, variant_name: _, bindings } => {
                // Check enum exists
                if self.scopes.lookup(&enum_name.name).is_none() {
                    self.error(format!("unknown enum '{}'", enum_name.name), enum_name.span);
                }
                for binding in bindings {
                    self.resolve_pattern(binding);
                }
            }
            parser::PatternKind::Tuple(patterns) => {
                for p in patterns {
                    self.resolve_pattern(p);
                }
            }
            parser::PatternKind::Or(patterns) => {
                // All patterns in an Or should bind the same variables
                // For now just resolve each
                for p in patterns {
                    self.resolve_pattern(p);
                }
            }
        }
    }
}

impl Default for Resolver {
    fn default() -> Self {
        Self::new()
    }
}
