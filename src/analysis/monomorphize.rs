//! Monomorphization pass
//!
//! Transforms generic functions into concrete specialized versions.
//! For each unique instantiation like `hmac::<Sha256State>(...)`, generates
//! a specialized function `hmac__Sha256State`.

use std::collections::{HashMap, HashSet};

use crate::errors::{AlgocError, AlgocResult};
use crate::parser::{
    Ast, Block, Expr, ExprKind, Function, Ident, Item, ItemKind, Param, Stmt, StmtKind, Type,
    TypeKind,
};

use super::scope::Scope;

/// A monomorphization request (generic function + concrete type arguments)
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
struct MonomorphKey {
    /// Name of the generic function
    func_name: String,
    /// Concrete type names for each type parameter
    type_args: Vec<String>,
}

impl MonomorphKey {
    /// Generate mangled name for the specialized function
    fn mangled_name(&self) -> String {
        if self.type_args.is_empty() {
            self.func_name.clone()
        } else {
            format!("{}__{}", self.func_name, self.type_args.join("_"))
        }
    }
}

/// Monomorphization pass
pub struct Monomorphizer<'a> {
    /// Global scope for interface/struct lookups
    global_scope: &'a Scope,
    /// Generic functions indexed by name
    generic_functions: HashMap<String, &'a Function>,
    /// Monomorphization requests found during traversal
    requests: HashSet<MonomorphKey>,
    /// Already generated specializations
    generated: HashMap<MonomorphKey, Function>,
    /// Errors collected during monomorphization
    errors: Vec<AlgocError>,
}

impl<'a> Monomorphizer<'a> {
    pub fn new(global_scope: &'a Scope) -> Self {
        Self {
            global_scope,
            generic_functions: HashMap::new(),
            requests: HashSet::new(),
            generated: HashMap::new(),
            errors: Vec::new(),
        }
    }

    /// Monomorphize the AST, generating specialized functions
    pub fn monomorphize(mut self, ast: &'a Ast) -> AlgocResult<Ast> {
        // First pass: collect generic functions
        for item in &ast.items {
            if let ItemKind::Function(func) = &item.kind {
                if func.type_params.is_some() {
                    self.generic_functions
                        .insert(func.name.name.clone(), func);
                }
            }
        }

        // Second pass: find all generic call sites
        for item in &ast.items {
            self.scan_item(item);
        }

        // Generate specialized functions for each request
        let requests: Vec<_> = self.requests.iter().cloned().collect();
        for key in requests {
            if !self.generated.contains_key(&key) {
                if let Some(specialized) = self.generate_specialized(&key) {
                    self.generated.insert(key, specialized);
                }
            }
        }

        if !self.errors.is_empty() {
            return Err(self.errors.remove(0));
        }

        // Build new AST with specialized functions added and generic calls rewritten
        let mut new_items = Vec::new();

        for item in &ast.items {
            match &item.kind {
                ItemKind::Function(func) => {
                    if func.type_params.is_some() {
                        // Skip generic functions from output (they're templates)
                        continue;
                    }
                    // Rewrite generic calls in function bodies
                    let rewritten = self.rewrite_item(item);
                    new_items.push(rewritten);
                }
                ItemKind::Impl(_impl_def) => {
                    // Rewrite generic calls in impl methods
                    let rewritten = self.rewrite_item(item);
                    new_items.push(rewritten);
                }
                ItemKind::Test(_test) => {
                    // Rewrite generic calls in tests
                    let rewritten = self.rewrite_item(item);
                    new_items.push(rewritten);
                }
                _ => {
                    new_items.push(item.clone());
                }
            }
        }

        // Add generated specialized functions
        for (_key, func) in &self.generated {
            new_items.push(Item {
                kind: ItemKind::Function(func.clone()),
                span: func.name.span,
            });
        }

        Ok(Ast { items: new_items })
    }

    /// Scan an item for generic calls
    fn scan_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => {
                if func.type_params.is_none() {
                    // Only scan non-generic functions
                    self.scan_block(&func.body);
                }
            }
            ItemKind::Impl(impl_def) => {
                for method in &impl_def.methods {
                    self.scan_block(&method.body);
                }
            }
            ItemKind::Test(test) => {
                self.scan_block(&test.body);
            }
            _ => {}
        }
    }

    fn scan_block(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.scan_stmt(stmt);
        }
    }

    fn scan_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Expr(expr) => self.scan_expr(expr),
            StmtKind::Let { init, .. } => {
                if let Some(init) = init {
                    self.scan_expr(init);
                }
            }
            StmtKind::Assign { target, value } => {
                self.scan_expr(target);
                self.scan_expr(value);
            }
            StmtKind::CompoundAssign { target, value, .. } => {
                self.scan_expr(target);
                self.scan_expr(value);
            }
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.scan_expr(condition);
                self.scan_block(then_block);
                if let Some(else_block) = else_block {
                    self.scan_block(else_block);
                }
            }
            StmtKind::For { start, end, body, .. } => {
                self.scan_expr(start);
                self.scan_expr(end);
                self.scan_block(body);
            }
            StmtKind::While { condition, body } => {
                self.scan_expr(condition);
                self.scan_block(body);
            }
            StmtKind::Loop { body } => {
                self.scan_block(body);
            }
            StmtKind::Return(Some(expr)) => {
                self.scan_expr(expr);
            }
            StmtKind::Block(block) => {
                self.scan_block(block);
            }
            _ => {}
        }
    }

    fn scan_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::GenericCall {
                func,
                type_args,
                args,
            } => {
                // Record this instantiation
                if let ExprKind::Ident(ident) = &func.kind {
                    let type_arg_names: Vec<String> = type_args
                        .iter()
                        .map(|t| self.type_to_name(t))
                        .collect();

                    self.requests.insert(MonomorphKey {
                        func_name: ident.name.clone(),
                        type_args: type_arg_names,
                    });
                }

                // Also scan the arguments
                for arg in args {
                    self.scan_expr(arg);
                }
            }
            ExprKind::Binary { left, right, .. } => {
                self.scan_expr(left);
                self.scan_expr(right);
            }
            ExprKind::Unary { operand, .. } => {
                self.scan_expr(operand);
            }
            ExprKind::Call { func, args } => {
                self.scan_expr(func);
                for arg in args {
                    self.scan_expr(arg);
                }
            }
            ExprKind::Index { array, index } => {
                self.scan_expr(array);
                self.scan_expr(index);
            }
            ExprKind::Field { object, .. } => {
                self.scan_expr(object);
            }
            ExprKind::Array(elements) => {
                for elem in elements {
                    self.scan_expr(elem);
                }
            }
            ExprKind::StructLit { fields, .. } => {
                for (_, value) in fields {
                    self.scan_expr(value);
                }
            }
            ExprKind::TypeStaticCall { args, .. } => {
                for arg in args {
                    self.scan_expr(arg);
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                self.scan_expr(receiver);
                for arg in args {
                    self.scan_expr(arg);
                }
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                self.scan_expr(condition);
                self.scan_expr(then_expr);
                self.scan_expr(else_expr);
            }
            ExprKind::Cast { expr, .. } => {
                self.scan_expr(expr);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Deref(inner) | ExprKind::Paren(inner) => {
                self.scan_expr(inner);
            }
            _ => {}
        }
    }

    /// Convert a Type to a simple name string for mangling
    fn type_to_name(&self, ty: &Type) -> String {
        match &ty.kind {
            TypeKind::Named(ident) => ident.name.clone(),
            TypeKind::Primitive(p) => format!("{:?}", p),
            TypeKind::Array { element, size } => {
                format!("{}_{}", self.type_to_name(element), size)
            }
            _ => "unknown".to_string(),
        }
    }

    /// Generate a specialized version of a generic function
    fn generate_specialized(&mut self, key: &MonomorphKey) -> Option<Function> {
        let generic_func = self.generic_functions.get(&key.func_name)?;
        let type_params = generic_func.type_params.as_ref()?;

        // Build substitution map: type param name -> concrete type name
        let mut subst: HashMap<String, String> = HashMap::new();
        for (param, concrete) in type_params.iter().zip(key.type_args.iter()) {
            subst.insert(param.name.name.clone(), concrete.clone());

            // Check interface constraint if present
            if let Some(ref _constraint) = param.constraint {
                // TODO: Call check_interface_satisfaction here
                // For now, we'll skip the check
            }
        }

        // Clone and transform the function
        let mut specialized = (*generic_func).clone();
        specialized.name = Ident::new(key.mangled_name(), generic_func.name.span);
        specialized.type_params = None; // No longer generic

        // Substitute type parameters in params and return type
        specialized.params = specialized
            .params
            .iter()
            .map(|p| Param {
                name: p.name.clone(),
                ty: self.substitute_type(&p.ty, &subst),
                span: p.span,
            })
            .collect();

        if let Some(ref ret_ty) = specialized.return_type {
            specialized.return_type = Some(self.substitute_type(ret_ty, &subst));
        }

        // Transform the body: replace H::method() calls with ConcreteType::method()
        specialized.body = self.transform_block(&specialized.body, &subst);

        Some(specialized)
    }

    /// Substitute type parameters in a type
    fn substitute_type(&self, ty: &Type, subst: &HashMap<String, String>) -> Type {
        match &ty.kind {
            TypeKind::Named(ident) => {
                if let Some(concrete) = subst.get(&ident.name) {
                    Type {
                        kind: TypeKind::Named(Ident::new(concrete.clone(), ident.span)),
                        span: ty.span,
                    }
                } else {
                    ty.clone()
                }
            }
            TypeKind::Ref(inner) => Type {
                kind: TypeKind::Ref(Box::new(self.substitute_type(inner, subst))),
                span: ty.span,
            },
            TypeKind::MutRef(inner) => Type {
                kind: TypeKind::MutRef(Box::new(self.substitute_type(inner, subst))),
                span: ty.span,
            },
            TypeKind::Array { element, size } => Type {
                kind: TypeKind::Array {
                    element: Box::new(self.substitute_type(element, subst)),
                    size: *size,
                },
                span: ty.span,
            },
            TypeKind::Slice { element } => Type {
                kind: TypeKind::Slice {
                    element: Box::new(self.substitute_type(element, subst)),
                },
                span: ty.span,
            },
            _ => ty.clone(),
        }
    }

    /// Transform a block, substituting type parameter calls
    fn transform_block(&self, block: &Block, subst: &HashMap<String, String>) -> Block {
        Block {
            stmts: block
                .stmts
                .iter()
                .map(|s| self.transform_stmt(s, subst))
                .collect(),
            span: block.span,
        }
    }

    fn transform_stmt(&self, stmt: &Stmt, subst: &HashMap<String, String>) -> Stmt {
        let kind = match &stmt.kind {
            StmtKind::Expr(expr) => StmtKind::Expr(self.transform_expr(expr, subst)),
            StmtKind::Let {
                name,
                ty,
                mutable,
                init,
            } => StmtKind::Let {
                name: name.clone(),
                ty: ty.as_ref().map(|t| self.substitute_type(t, subst)),
                mutable: *mutable,
                init: init.as_ref().map(|e| self.transform_expr(e, subst)),
            },
            StmtKind::Assign { target, value } => StmtKind::Assign {
                target: self.transform_expr(target, subst),
                value: self.transform_expr(value, subst),
            },
            StmtKind::CompoundAssign { target, op, value } => StmtKind::CompoundAssign {
                target: self.transform_expr(target, subst),
                op: *op,
                value: self.transform_expr(value, subst),
            },
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => StmtKind::If {
                condition: self.transform_expr(condition, subst),
                then_block: self.transform_block(then_block, subst),
                else_block: else_block.as_ref().map(|b| self.transform_block(b, subst)),
            },
            StmtKind::For {
                var,
                start,
                end,
                inclusive,
                body,
            } => StmtKind::For {
                var: var.clone(),
                start: self.transform_expr(start, subst),
                end: self.transform_expr(end, subst),
                inclusive: *inclusive,
                body: self.transform_block(body, subst),
            },
            StmtKind::While { condition, body } => StmtKind::While {
                condition: self.transform_expr(condition, subst),
                body: self.transform_block(body, subst),
            },
            StmtKind::Loop { body } => StmtKind::Loop {
                body: self.transform_block(body, subst),
            },
            StmtKind::Return(expr) => {
                StmtKind::Return(expr.as_ref().map(|e| self.transform_expr(e, subst)))
            }
            StmtKind::Block(block) => StmtKind::Block(self.transform_block(block, subst)),
            StmtKind::Break => StmtKind::Break,
            StmtKind::Continue => StmtKind::Continue,
        };
        Stmt {
            kind,
            span: stmt.span,
        }
    }

    fn transform_expr(&self, expr: &Expr, subst: &HashMap<String, String>) -> Expr {
        let kind = match &expr.kind {
            // Transform H::method() to ConcreteType::method()
            ExprKind::TypeStaticCall {
                type_name,
                method_name,
                args,
            } => {
                let new_type_name = if let Some(concrete) = subst.get(&type_name.name) {
                    Ident::new(concrete.clone(), type_name.span)
                } else {
                    type_name.clone()
                };
                ExprKind::TypeStaticCall {
                    type_name: new_type_name,
                    method_name: method_name.clone(),
                    args: args.iter().map(|a| self.transform_expr(a, subst)).collect(),
                }
            }
            // Transform generic calls to regular calls
            ExprKind::GenericCall {
                func,
                type_args,
                args,
            } => {
                if let ExprKind::Ident(ident) = &func.kind {
                    let type_arg_names: Vec<String> = type_args
                        .iter()
                        .map(|t| self.type_to_name(t))
                        .collect();
                    let key = MonomorphKey {
                        func_name: ident.name.clone(),
                        type_args: type_arg_names,
                    };
                    let mangled = key.mangled_name();

                    ExprKind::Call {
                        func: Box::new(Expr {
                            kind: ExprKind::Ident(Ident::new(mangled, ident.span)),
                            span: func.span,
                        }),
                        args: args.iter().map(|a| self.transform_expr(a, subst)).collect(),
                    }
                } else {
                    // Shouldn't happen but handle it
                    expr.kind.clone()
                }
            }
            ExprKind::Binary { left, op, right } => ExprKind::Binary {
                left: Box::new(self.transform_expr(left, subst)),
                op: *op,
                right: Box::new(self.transform_expr(right, subst)),
            },
            ExprKind::Unary { op, operand } => ExprKind::Unary {
                op: *op,
                operand: Box::new(self.transform_expr(operand, subst)),
            },
            ExprKind::Call { func, args } => ExprKind::Call {
                func: Box::new(self.transform_expr(func, subst)),
                args: args.iter().map(|a| self.transform_expr(a, subst)).collect(),
            },
            ExprKind::Index { array, index } => ExprKind::Index {
                array: Box::new(self.transform_expr(array, subst)),
                index: Box::new(self.transform_expr(index, subst)),
            },
            ExprKind::Field { object, field } => ExprKind::Field {
                object: Box::new(self.transform_expr(object, subst)),
                field: field.clone(),
            },
            ExprKind::Array(elements) => ExprKind::Array(
                elements.iter().map(|e| self.transform_expr(e, subst)).collect(),
            ),
            ExprKind::StructLit { name, fields } => ExprKind::StructLit {
                name: name.clone(),
                fields: fields
                    .iter()
                    .map(|(n, v)| (n.clone(), self.transform_expr(v, subst)))
                    .collect(),
            },
            ExprKind::MethodCall {
                receiver,
                method_name,
                mangled_name,
                args,
            } => ExprKind::MethodCall {
                receiver: Box::new(self.transform_expr(receiver, subst)),
                method_name: method_name.clone(),
                mangled_name: mangled_name.clone(),
                args: args.iter().map(|a| self.transform_expr(a, subst)).collect(),
            },
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => ExprKind::Conditional {
                condition: Box::new(self.transform_expr(condition, subst)),
                then_expr: Box::new(self.transform_expr(then_expr, subst)),
                else_expr: Box::new(self.transform_expr(else_expr, subst)),
            },
            ExprKind::Cast { expr: inner, ty } => ExprKind::Cast {
                expr: Box::new(self.transform_expr(inner, subst)),
                ty: self.substitute_type(ty, subst),
            },
            ExprKind::Ref(inner) => {
                ExprKind::Ref(Box::new(self.transform_expr(inner, subst)))
            }
            ExprKind::MutRef(inner) => {
                ExprKind::MutRef(Box::new(self.transform_expr(inner, subst)))
            }
            ExprKind::Deref(inner) => {
                ExprKind::Deref(Box::new(self.transform_expr(inner, subst)))
            }
            ExprKind::Paren(inner) => {
                ExprKind::Paren(Box::new(self.transform_expr(inner, subst)))
            }
            _ => expr.kind.clone(),
        };
        Expr {
            kind,
            span: expr.span,
        }
    }

    /// Rewrite an item (transforming generic calls to regular calls)
    fn rewrite_item(&self, item: &Item) -> Item {
        let empty_subst = HashMap::new();
        let kind = match &item.kind {
            ItemKind::Function(func) => ItemKind::Function(Function {
                name: func.name.clone(),
                type_params: func.type_params.clone(),
                params: func.params.clone(),
                return_type: func.return_type.clone(),
                body: self.transform_block(&func.body, &empty_subst),
                is_static: func.is_static,
            }),
            ItemKind::Impl(impl_def) => ItemKind::Impl(crate::parser::ImplDef {
                target: impl_def.target.clone(),
                methods: impl_def
                    .methods
                    .iter()
                    .map(|m| Function {
                        name: m.name.clone(),
                        type_params: m.type_params.clone(),
                        params: m.params.clone(),
                        return_type: m.return_type.clone(),
                        body: self.transform_block(&m.body, &empty_subst),
                        is_static: m.is_static,
                    })
                    .collect(),
                span: impl_def.span,
            }),
            ItemKind::Test(test) => ItemKind::Test(crate::parser::TestDef {
                name: test.name.clone(),
                body: self.transform_block(&test.body, &empty_subst),
                span: test.span,
            }),
            _ => item.kind.clone(),
        };
        Item {
            kind,
            span: item.span,
        }
    }
}
