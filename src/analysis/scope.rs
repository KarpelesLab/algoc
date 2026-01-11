//! Symbol tables and scopes for name resolution
//!
//! Manages the mapping from names to their definitions.

use std::collections::HashMap;
use crate::errors::SourceSpan;
use super::types::Type;

/// A scope containing symbol definitions
#[derive(Debug, Clone)]
pub struct Scope {
    /// Symbols defined in this scope
    symbols: HashMap<String, Symbol>,
    /// Struct definitions
    structs: HashMap<String, StructDef>,
    /// Enum definitions
    enums: HashMap<String, EnumDef>,
    /// Child scopes (for functions, blocks, etc.)
    children: Vec<Scope>,
}

impl Scope {
    /// Create a new empty scope
    pub fn new() -> Self {
        Self {
            symbols: HashMap::new(),
            structs: HashMap::new(),
            enums: HashMap::new(),
            children: Vec::new(),
        }
    }

    /// Define a symbol in this scope
    pub fn define(&mut self, name: String, symbol: Symbol) -> Result<(), String> {
        if self.symbols.contains_key(&name) {
            return Err(format!("symbol '{}' is already defined in this scope", name));
        }
        self.symbols.insert(name, symbol);
        Ok(())
    }

    /// Define a struct in this scope
    pub fn define_struct(&mut self, name: String, def: StructDef) -> Result<(), String> {
        if self.structs.contains_key(&name) {
            return Err(format!("struct '{}' is already defined", name));
        }
        self.structs.insert(name, def);
        Ok(())
    }

    /// Look up a symbol by name in this scope only
    pub fn get(&self, name: &str) -> Option<&Symbol> {
        self.symbols.get(name)
    }

    /// Look up a struct by name
    pub fn get_struct(&self, name: &str) -> Option<&StructDef> {
        self.structs.get(name)
    }

    /// Look up a struct by name (mutable)
    pub fn get_struct_mut(&mut self, name: &str) -> Option<&mut StructDef> {
        self.structs.get_mut(name)
    }

    /// Define an enum in this scope
    pub fn define_enum(&mut self, name: String, def: EnumDef) -> Result<(), String> {
        if self.enums.contains_key(&name) {
            return Err(format!("enum '{}' is already defined", name));
        }
        self.enums.insert(name, def);
        Ok(())
    }

    /// Look up an enum by name
    pub fn get_enum(&self, name: &str) -> Option<&EnumDef> {
        self.enums.get(name)
    }

    /// Get all symbols in this scope
    pub fn symbols(&self) -> impl Iterator<Item = (&String, &Symbol)> {
        self.symbols.iter()
    }

    /// Get all structs in this scope
    pub fn structs(&self) -> impl Iterator<Item = (&String, &StructDef)> {
        self.structs.iter()
    }

    /// Add a child scope
    pub fn add_child(&mut self, child: Scope) {
        self.children.push(child);
    }

    /// Get child scopes
    pub fn children(&self) -> &[Scope] {
        &self.children
    }
}

impl Default for Scope {
    fn default() -> Self {
        Self::new()
    }
}

/// A symbol in the symbol table
#[derive(Debug, Clone)]
pub struct Symbol {
    /// The kind of symbol
    pub kind: SymbolKind,
    /// The type of this symbol
    pub ty: Type,
    /// Source location where this symbol was defined
    pub span: SourceSpan,
    /// Whether this symbol is mutable (for variables)
    pub mutable: bool,
}

impl Symbol {
    /// Create a new variable symbol
    pub fn variable(ty: Type, span: SourceSpan, mutable: bool) -> Self {
        Self {
            kind: SymbolKind::Variable,
            ty,
            span,
            mutable,
        }
    }

    /// Create a new constant symbol
    pub fn constant(ty: Type, span: SourceSpan) -> Self {
        Self {
            kind: SymbolKind::Constant,
            ty,
            span,
            mutable: false,
        }
    }

    /// Create a new function symbol
    pub fn function(ty: Type, span: SourceSpan) -> Self {
        Self {
            kind: SymbolKind::Function,
            ty,
            span,
            mutable: false,
        }
    }

    /// Create a new parameter symbol
    pub fn parameter(ty: Type, span: SourceSpan) -> Self {
        Self {
            kind: SymbolKind::Parameter,
            ty,
            span,
            mutable: false,
        }
    }
}

/// The kind of a symbol
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    /// A local variable
    Variable,
    /// A constant
    Constant,
    /// A function
    Function,
    /// A function parameter
    Parameter,
}

/// A struct definition
#[derive(Debug, Clone)]
pub struct StructDef {
    /// The name of the struct
    pub name: String,
    /// Fields of the struct
    pub fields: Vec<StructField>,
    /// Methods defined for this struct (method name -> mangled function name)
    pub methods: HashMap<String, String>,
    /// Source location
    pub span: SourceSpan,
}

impl StructDef {
    /// Create a new struct definition
    pub fn new(name: String, span: SourceSpan) -> Self {
        Self {
            name,
            fields: Vec::new(),
            methods: HashMap::new(),
            span,
        }
    }

    /// Add a field to the struct
    pub fn add_field(&mut self, field: StructField) {
        self.fields.push(field);
    }

    /// Get a field by name
    pub fn get_field(&self, name: &str) -> Option<&StructField> {
        self.fields.iter().find(|f| f.name == name)
    }

    /// Get the index of a field by name
    pub fn field_index(&self, name: &str) -> Option<usize> {
        self.fields.iter().position(|f| f.name == name)
    }

    /// Add a method to the struct
    pub fn add_method(&mut self, name: String, mangled_name: String) {
        self.methods.insert(name, mangled_name);
    }

    /// Get a method's mangled name by its short name
    pub fn get_method(&self, name: &str) -> Option<&String> {
        self.methods.get(name)
    }
}

/// A field in a struct
#[derive(Debug, Clone)]
pub struct StructField {
    /// Field name
    pub name: String,
    /// Field type
    pub ty: Type,
    /// Source location
    pub span: SourceSpan,
}

impl StructField {
    pub fn new(name: String, ty: Type, span: SourceSpan) -> Self {
        Self { name, ty, span }
    }
}

/// An enum definition
#[derive(Debug, Clone)]
pub struct EnumDef {
    /// The name of the enum
    pub name: String,
    /// Variants of the enum
    pub variants: Vec<EnumVariantDef>,
    /// Source location
    pub span: SourceSpan,
}

impl EnumDef {
    /// Create a new enum definition
    pub fn new(name: String, span: SourceSpan) -> Self {
        Self {
            name,
            variants: Vec::new(),
            span,
        }
    }

    /// Add a variant to the enum
    pub fn add_variant(&mut self, variant: EnumVariantDef) {
        self.variants.push(variant);
    }

    /// Get a variant by name
    pub fn get_variant(&self, name: &str) -> Option<&EnumVariantDef> {
        self.variants.iter().find(|v| v.name == name)
    }
}

/// A variant in an enum
#[derive(Debug, Clone)]
pub struct EnumVariantDef {
    /// Variant name
    pub name: String,
    /// Types of the variant's data (empty for unit variants)
    pub data_types: Vec<Type>,
    /// Source location
    pub span: SourceSpan,
}

impl EnumVariantDef {
    pub fn new(name: String, data_types: Vec<Type>, span: SourceSpan) -> Self {
        Self { name, data_types, span }
    }
}

/// A scope stack for tracking nested scopes during resolution
#[derive(Debug)]
pub struct ScopeStack {
    /// Stack of scopes (innermost is last)
    scopes: Vec<Scope>,
}

impl ScopeStack {
    /// Create a new scope stack with a global scope
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::new()],
        }
    }

    /// Push a new scope onto the stack
    pub fn push(&mut self) {
        self.scopes.push(Scope::new());
    }

    /// Pop the innermost scope and return it
    pub fn pop(&mut self) -> Option<Scope> {
        if self.scopes.len() > 1 {
            self.scopes.pop()
        } else {
            None // Don't pop the global scope
        }
    }

    /// Get the current (innermost) scope mutably
    pub fn current_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().expect("scope stack should never be empty")
    }

    /// Get the global (outermost) scope
    pub fn global(&self) -> &Scope {
        self.scopes.first().expect("scope stack should never be empty")
    }

    /// Get the global scope mutably
    pub fn global_mut(&mut self) -> &mut Scope {
        self.scopes.first_mut().expect("scope stack should never be empty")
    }

    /// Define a symbol in the current scope
    pub fn define(&mut self, name: String, symbol: Symbol) -> Result<(), String> {
        self.current_mut().define(name, symbol)
    }

    /// Look up a symbol by name, searching from innermost to outermost scope
    pub fn lookup(&self, name: &str) -> Option<&Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(sym) = scope.get(name) {
                return Some(sym);
            }
        }
        None
    }

    /// Look up a struct by name (only in global scope)
    pub fn lookup_struct(&self, name: &str) -> Option<&StructDef> {
        self.global().get_struct(name)
    }

    /// Look up an enum by name (only in global scope)
    pub fn lookup_enum(&self, name: &str) -> Option<&EnumDef> {
        self.global().get_enum(name)
    }

    /// Consume the stack and return the global scope with all nested scopes
    pub fn into_global(mut self) -> Scope {
        // Pop all scopes except global, adding them as children
        while self.scopes.len() > 1 {
            let child = self.scopes.pop().unwrap();
            self.current_mut().add_child(child);
        }
        self.scopes.pop().unwrap()
    }
}

impl Default for ScopeStack {
    fn default() -> Self {
        Self::new()
    }
}
