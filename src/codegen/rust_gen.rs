//! Rust code generator
//!
//! Generates Rust code from the analyzed AST.
//! Produces self-contained, compilable Rust source files.

use super::CodeGenerator;
use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;
use crate::parser::{
    Ast, BinaryOp, Block, BuiltinFunc, Expr, ExprKind, Function, Item, ItemKind, Stmt, StmtKind,
    Type as ParserType, UnaryOp,
};
use std::collections::HashMap;

/// Struct field info for code generation
#[derive(Clone)]
struct StructFieldInfo {
    name: String,
    ty: ParserType,
}

/// Struct method info (method name -> mangled function name)
type MethodMap = HashMap<String, String>;

/// Rust code generator
pub struct RustGenerator {
    /// Current indentation level
    indent: usize,
    /// Output buffer
    output: String,
    /// Whether to include test functions and runner
    include_tests: bool,
    /// Struct definitions for read/write generation
    struct_defs: HashMap<String, Vec<StructFieldInfo>>,
    /// Struct methods: struct_name -> (method_name -> mangled_name)
    struct_methods: HashMap<String, MethodMap>,
    /// Variable types (for struct read/write generation)
    var_types: HashMap<String, String>,
    /// Variable Rust primitive types (for type-aware code generation, e.g. "u32", "u64")
    var_rust_types: HashMap<String, String>,
    /// Function parameter Rust types
    param_rust_types: HashMap<String, String>,
    /// Function return types (function_name -> rust_type)
    func_return_types: HashMap<String, String>,
    /// Context type hint for expression generation (e.g., from let binding)
    /// Used as fallback for wrapping suffix inference
    type_hint: Option<String>,
}

impl RustGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            var_rust_types: HashMap::new(),
            param_rust_types: HashMap::new(),
            func_return_types: HashMap::new(),
            type_hint: None,
        }
    }

    /// Set whether to include tests in the output
    pub fn with_tests(mut self, include: bool) -> Self {
        self.include_tests = include;
        self
    }

    fn write(&mut self, s: &str) {
        self.output.push_str(s);
    }

    fn writeln(&mut self, s: &str) {
        self.write_indent();
        self.output.push_str(s);
        self.output.push('\n');
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.output.push_str("    ");
        }
    }

    fn indent(&mut self) {
        self.indent += 1;
    }

    fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        // Reader struct for streaming byte input
        self.writeln("#[derive(Clone)]");
        self.writeln("struct Reader {");
        self.indent();
        self.writeln("data: Vec<u8>,");
        self.writeln("pos: usize,");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("impl Reader {");
        self.indent();

        self.writeln("fn new(data: Vec<u8>) -> Self {");
        self.indent();
        self.writeln("Reader { data, pos: 0 }");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u8
        self.writeln("fn read_u8(&mut self) -> u8 {");
        self.indent();
        self.writeln("let v = self.data[self.pos];");
        self.writeln("self.pos += 1;");
        self.writeln("v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u16 variants
        self.writeln("fn read_u16(&mut self) -> u16 { self.read_u16be() }");
        self.writeln("fn read_u16be(&mut self) -> u16 {");
        self.indent();
        self.writeln("let v = u16::from_be_bytes([self.data[self.pos], self.data[self.pos + 1]]);");
        self.writeln("self.pos += 2;");
        self.writeln("v");
        self.dedent();
        self.writeln("}");
        self.writeln("fn read_u16le(&mut self) -> u16 {");
        self.indent();
        self.writeln("let v = u16::from_le_bytes([self.data[self.pos], self.data[self.pos + 1]]);");
        self.writeln("self.pos += 2;");
        self.writeln("v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u32 variants
        self.writeln("fn read_u32(&mut self) -> u32 { self.read_u32be() }");
        self.writeln("fn read_u32be(&mut self) -> u32 {");
        self.indent();
        self.writeln("let b = &self.data[self.pos..self.pos + 4];");
        self.writeln("let v = u32::from_be_bytes([b[0], b[1], b[2], b[3]]);");
        self.writeln("self.pos += 4;");
        self.writeln("v");
        self.dedent();
        self.writeln("}");
        self.writeln("fn read_u32le(&mut self) -> u32 {");
        self.indent();
        self.writeln("let b = &self.data[self.pos..self.pos + 4];");
        self.writeln("let v = u32::from_le_bytes([b[0], b[1], b[2], b[3]]);");
        self.writeln("self.pos += 4;");
        self.writeln("v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u64 variants
        self.writeln("fn read_u64(&mut self) -> u64 { self.read_u64be() }");
        self.writeln("fn read_u64be(&mut self) -> u64 {");
        self.indent();
        self.writeln("let b = &self.data[self.pos..self.pos + 8];");
        self.writeln(
            "let v = u64::from_be_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);",
        );
        self.writeln("self.pos += 8;");
        self.writeln("v");
        self.dedent();
        self.writeln("}");
        self.writeln("fn read_u64le(&mut self) -> u64 {");
        self.indent();
        self.writeln("let b = &self.data[self.pos..self.pos + 8];");
        self.writeln(
            "let v = u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);",
        );
        self.writeln("self.pos += 8;");
        self.writeln("v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_bytes
        self.writeln("fn read_bytes(&mut self, count: usize) -> Vec<u8> {");
        self.indent();
        self.writeln("let result = self.data[self.pos..self.pos + count].to_vec();");
        self.writeln("self.pos += count;");
        self.writeln("result");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_chunk
        self.writeln("fn read_chunk(&mut self, max_size: usize) -> Vec<u8> {");
        self.indent();
        self.writeln("let remaining = self.data.len() - self.pos;");
        self.writeln("let count = max_size.min(remaining);");
        self.writeln("let result = self.data[self.pos..self.pos + count].to_vec();");
        self.writeln("self.pos += count;");
        self.writeln("result");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // eof
        self.writeln("fn eof(&self) -> bool { self.pos >= self.data.len() }");

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer struct for streaming byte output
        self.writeln("#[derive(Clone)]");
        self.writeln("struct Writer {");
        self.indent();
        self.writeln("data: Vec<u8>,");
        self.writeln("pos: usize,");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("impl Writer {");
        self.indent();

        self.writeln("fn new(data: Vec<u8>) -> Self {");
        self.indent();
        self.writeln("let pos = 0;");
        self.writeln("Writer { data, pos }");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u8
        self.writeln("fn write_u8(&mut self, v: u8) {");
        self.indent();
        self.writeln("self.data[self.pos] = v;");
        self.writeln("self.pos += 1;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u16 variants
        self.writeln("fn write_u16(&mut self, v: u16) { self.write_u16be(v); }");
        self.writeln("fn write_u16be(&mut self, v: u16) {");
        self.indent();
        self.writeln("let bytes = v.to_be_bytes();");
        self.writeln("self.data[self.pos..self.pos + 2].copy_from_slice(&bytes);");
        self.writeln("self.pos += 2;");
        self.dedent();
        self.writeln("}");
        self.writeln("fn write_u16le(&mut self, v: u16) {");
        self.indent();
        self.writeln("let bytes = v.to_le_bytes();");
        self.writeln("self.data[self.pos..self.pos + 2].copy_from_slice(&bytes);");
        self.writeln("self.pos += 2;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u32 variants
        self.writeln("fn write_u32(&mut self, v: u32) { self.write_u32be(v); }");
        self.writeln("fn write_u32be(&mut self, v: u32) {");
        self.indent();
        self.writeln("let bytes = v.to_be_bytes();");
        self.writeln("self.data[self.pos..self.pos + 4].copy_from_slice(&bytes);");
        self.writeln("self.pos += 4;");
        self.dedent();
        self.writeln("}");
        self.writeln("fn write_u32le(&mut self, v: u32) {");
        self.indent();
        self.writeln("let bytes = v.to_le_bytes();");
        self.writeln("self.data[self.pos..self.pos + 4].copy_from_slice(&bytes);");
        self.writeln("self.pos += 4;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u64 variants
        self.writeln("fn write_u64(&mut self, v: u64) { self.write_u64be(v); }");
        self.writeln("fn write_u64be(&mut self, v: u64) {");
        self.indent();
        self.writeln("let bytes = v.to_be_bytes();");
        self.writeln("self.data[self.pos..self.pos + 8].copy_from_slice(&bytes);");
        self.writeln("self.pos += 8;");
        self.dedent();
        self.writeln("}");
        self.writeln("fn write_u64le(&mut self, v: u64) {");
        self.indent();
        self.writeln("let bytes = v.to_le_bytes();");
        self.writeln("self.data[self.pos..self.pos + 8].copy_from_slice(&bytes);");
        self.writeln("self.pos += 8;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_bytes
        self.writeln("fn write_bytes(&mut self, data: &[u8]) {");
        self.indent();
        self.writeln("self.data[self.pos..self.pos + data.len()].copy_from_slice(data);");
        self.writeln("self.pos += data.len();");
        self.dedent();
        self.writeln("}");

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Generate test runtime helpers (only when include_tests is true)
    fn generate_test_runtime(&mut self) {
        self.writeln("// Test Helpers");
        self.writeln("static mut __TEST_FAILURES: i32 = 0;");
        self.writeln("static mut __TEST_NAME: &str = \"\";");
        self.writeln("");

        self.writeln("fn __assert(condition: bool) {");
        self.indent();
        self.writeln("unsafe {");
        self.indent();
        self.writeln("if !condition {");
        self.indent();
        self.writeln("__TEST_FAILURES += 1;");
        self.writeln("eprintln!(\"  ASSERTION FAILED in {}\", __TEST_NAME);");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_ast(&mut self, ast: &Ast) {
        for item in &ast.items {
            self.generate_item(item);
        }
    }

    fn generate_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => self.generate_function(func),
            ItemKind::Const(c) => self.generate_const(c),
            ItemKind::Struct(s) => self.generate_struct(s),
            ItemKind::Layout(l) => self.generate_layout(l),
            ItemKind::Enum(e) => self.generate_enum(e),
            ItemKind::Test(test) => {
                if self.include_tests {
                    self.generate_test(test);
                }
            }
            ItemKind::Use(_) => {
                // Use statements are handled during loading, items are already merged
            }
            ItemKind::Impl(impl_def) => {
                // Generate methods as standalone functions with mangled names
                for method in &impl_def.methods {
                    self.generate_method(&impl_def.target.name, method);
                }
            }
            ItemKind::Interface(_) => {
                // Interfaces are compile-time only, no runtime representation
            }
        }
    }

    fn generate_method(&mut self, struct_name: &str, func: &crate::parser::Function) {
        let mangled_name = format!("{}__{}", struct_name, func.name.name);

        self.write_indent();
        self.write(&format!("fn {}(", mangled_name));

        // Parameters - replace Self with the concrete struct name
        // Use param types (converts &[T; N] -> &[T] and &mut [T; N] -> &mut [T])
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            // Handle self parameter
            if param.name.name == "self" {
                self.write(&format!(
                    "self_: {}",
                    Self::rust_param_type(&param.ty, Some(struct_name))
                ));
            } else {
                self.write(&format!(
                    "{}: {}",
                    param.name.name,
                    Self::rust_param_type(&param.ty, Some(struct_name))
                ));
            }
        }

        self.write(")");

        // Return type - replace Self with the concrete struct name
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!(
                " -> {}",
                Self::rust_type_replacing_self(ret_ty, Some(struct_name))
            ));
        }

        self.write(" {\n");
        self.indent();
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("fn test_{}() {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        self.write(&format!(
            "const {}: {} = ",
            c.name.name,
            Self::rust_type(&c.ty)
        ));
        self.generate_expr(&c.value);
        self.write(";\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        let needs_lifetime = s.fields.iter().any(|f| Self::type_needs_lifetime(&f.ty));
        let has_mut_ref = s.fields.iter().any(|f| Self::type_contains_mut_ref(&f.ty));
        if !has_mut_ref {
            self.writeln("#[derive(Clone)]");
        }
        if needs_lifetime {
            self.writeln(&format!("struct {}<'a> {{", s.name.name));
        } else {
            self.writeln(&format!("struct {} {{", s.name.name));
        }
        self.indent();
        for field in &s.fields {
            if needs_lifetime {
                self.writeln(&format!(
                    "{}: {},",
                    field.name.name,
                    self.rust_type_with_lifetime(&field.ty)
                ));
            } else {
                self.writeln(&format!(
                    "{}: {},",
                    field.name.name,
                    Self::rust_type(&field.ty)
                ));
            }
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Generate a factory function for the struct (create_Name) - only if no lifetime needed
        if !needs_lifetime {
            self.writeln(&format!(
                "fn create_{}() -> {} {{",
                s.name.name, s.name.name
            ));
            self.indent();
            self.writeln(&format!("{} {{", s.name.name));
            self.indent();
            for field in &s.fields {
                let init = Self::default_value_for_type(&field.ty);
                self.writeln(&format!("{}: {},", field.name.name, init));
            }
            self.dedent();
            self.writeln("}");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        let needs_lifetime = l.fields.iter().any(|f| Self::type_needs_lifetime(&f.ty));
        let has_mut_ref = l.fields.iter().any(|f| Self::type_contains_mut_ref(&f.ty));
        // Layouts are similar to structs in Rust
        if !has_mut_ref {
            self.writeln("#[derive(Clone)]");
        }
        if needs_lifetime {
            self.writeln(&format!("struct {}<'a> {{", l.name.name));
        } else {
            self.writeln(&format!("struct {} {{", l.name.name));
        }
        self.indent();
        for field in &l.fields {
            if needs_lifetime {
                self.writeln(&format!(
                    "{}: {},",
                    field.name.name,
                    self.rust_type_with_lifetime(&field.ty)
                ));
            } else {
                self.writeln(&format!(
                    "{}: {},",
                    field.name.name,
                    Self::rust_type(&field.ty)
                ));
            }
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Generate a factory function - only if no lifetime needed
        if !needs_lifetime {
            self.writeln(&format!(
                "fn create_{}() -> {} {{",
                l.name.name, l.name.name
            ));
            self.indent();
            self.writeln(&format!("{} {{", l.name.name));
            self.indent();
            for field in &l.fields {
                let init = Self::default_value_for_type(&field.ty);
                self.writeln(&format!("{}: {},", field.name.name, init));
            }
            self.dedent();
            self.writeln("}");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        self.writeln("#[derive(Clone, PartialEq)]");
        self.writeln(&format!("enum {} {{", e.name.name));
        self.indent();
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!("{},", variant.name.name));
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    let type_strs: Vec<String> = types.iter().map(Self::rust_type).collect();
                    self.writeln(&format!("{}({}),", variant.name.name, type_strs.join(", ")));
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    self.writeln(&format!("{} {{", variant.name.name));
                    self.indent();
                    for field in fields {
                        self.writeln(&format!(
                            "{}: {},",
                            field.name.name,
                            Self::rust_type(&field.ty)
                        ));
                    }
                    self.dedent();
                    self.writeln("},");
                }
            }
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn default_value_for_type(ty: &crate::parser::Type) -> String {
        match &ty.kind {
            crate::parser::TypeKind::Primitive(p) => {
                if matches!(p, crate::parser::PrimitiveType::Bool) {
                    "false".to_string()
                } else {
                    "0".to_string()
                }
            }
            crate::parser::TypeKind::Array { element, size } => {
                let init = Self::default_value_for_type(element);
                format!("[{}; {}]", init, size)
            }
            crate::parser::TypeKind::Named(ident) => {
                format!("create_{}()", ident.name)
            }
            _ => "Default::default()".to_string(),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        // Clear per-function type tracking
        self.var_rust_types.clear();
        self.param_rust_types.clear();

        // Detect if this function was monomorphized from a method/generic
        // If the function name contains "__", the prefix is the struct name
        // Also check if any parameter or return type uses SelfType
        let self_replacement = Self::infer_self_type_name(&func.name.name, func);

        // Pre-pass: collect return type for this function
        if let Some(ret_ty) = &func.return_type {
            let rust_ty = Self::rust_type_replacing_self(ret_ty, self_replacement.as_deref());
            self.func_return_types
                .insert(func.name.name.clone(), rust_ty);
        }

        // Check if function needs lifetime annotations:
        // A function needs <'a> if it has both:
        // 1. A parameter that is a &mut struct-with-lifetime (e.g., &mut BitReader)
        // 2. A reference parameter that could be stored in that struct (&[u8], &mut [u8])
        let needs_lifetime = self.function_needs_lifetime(func);

        self.write_indent();
        if needs_lifetime {
            self.write(&format!("fn {}<'a>(", func.name.name));
        } else {
            self.write(&format!("fn {}(", func.name.name));
        }

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            let rust_ty = if needs_lifetime {
                self.rust_type_with_lifetime(&param.ty)
            } else {
                // Use param type (converts &[T; N] -> &[T] and &mut [T; N] -> &mut [T])
                Self::rust_param_type(&param.ty, self_replacement.as_deref())
            };
            // Check if this parameter needs `mut` (e.g., Reader/Writer that have &mut self methods)
            let needs_mut = matches!(&param.ty.kind,
                crate::parser::TypeKind::Named(ident) if ident.name == "Reader" || ident.name == "Writer"
            );

            // Handle self parameter
            if param.name.name == "self" {
                self.write(&format!("self_: {}", rust_ty));
                self.param_rust_types.insert("self_".to_string(), rust_ty);
            } else if needs_mut {
                self.write(&format!("mut {}: {}", param.name.name, rust_ty.clone()));
                self.param_rust_types
                    .insert(param.name.name.clone(), rust_ty);
            } else {
                self.write(&format!("{}: {}", param.name.name, rust_ty.clone()));
                self.param_rust_types
                    .insert(param.name.name.clone(), rust_ty);
            }
        }

        self.write(")");

        // Return type
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!(
                " -> {}",
                Self::rust_type_replacing_self(ret_ty, self_replacement.as_deref())
            ));
        }

        self.write(" {\n");
        self.indent();

        // Track variable types from parameters
        for param in &func.params {
            if let crate::parser::TypeKind::Named(type_ident) = &param.ty.kind {
                let param_name = if param.name.name == "self" {
                    "self_".to_string()
                } else {
                    param.name.name.clone()
                };
                self.var_types.insert(param_name, type_ident.name.clone());
            }
            // Also handle &mut StructName
            if let crate::parser::TypeKind::MutRef(inner) = &param.ty.kind
                && let crate::parser::TypeKind::Named(type_ident) = &inner.kind
            {
                let param_name = if param.name.name == "self" {
                    "self_".to_string()
                } else {
                    param.name.name.clone()
                };
                self.var_types.insert(param_name, type_ident.name.clone());
            }
        }

        self.generate_block(&func.body);

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_block(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.generate_stmt(stmt);
        }
    }

    fn generate_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let {
                name,
                ty,
                mutable,
                init,
            } => {
                // Track struct types for method resolution
                if let Some(ty) = ty
                    && let crate::parser::TypeKind::Named(type_ident) = &ty.kind
                {
                    self.var_types
                        .insert(name.name.clone(), type_ident.name.clone());
                }

                // Track Rust primitive types for type-aware code generation
                if let Some(ty) = ty {
                    let rust_ty = Self::rust_type(ty);
                    self.var_rust_types.insert(name.name.clone(), rust_ty);
                }

                // Also infer type from static method calls like TypeName__new()
                if let Some(init_expr) = init {
                    if let ExprKind::Call { func, .. } = &init_expr.kind
                        && let ExprKind::Ident(func_ident) = &func.kind
                        && let Some(idx) = func_ident.name.find("__new")
                    {
                        let struct_name = &func_ident.name[..idx];
                        self.var_types
                            .insert(name.name.clone(), struct_name.to_string());
                    }
                    if let ExprKind::TypeStaticCall {
                        type_name,
                        method_name,
                        ..
                    } = &init_expr.kind
                        && method_name.name == "new"
                    {
                        self.var_types
                            .insert(name.name.clone(), type_name.name.clone());
                    }
                }

                // Determine if the declared type should be adjusted for the init expression
                let skip_type_annotation = if let Some(ty) = ty
                    && let Some(init_expr) = init
                {
                    // If the declared type is a slice (&[u8]) but the init returns Vec<u8>
                    // (e.g., reader.read_chunk()), skip the type annotation to let Rust infer Vec<u8>
                    Self::type_is_slice_or_ref(ty) && Self::expr_returns_vec(init_expr)
                } else {
                    false
                };
                if skip_type_annotation {
                    // Track the variable as Vec<u8> so we can add & at call sites
                    self.var_rust_types
                        .insert(name.name.clone(), "Vec<u8>".to_string());
                }

                self.write_indent();
                if *mutable {
                    self.write("let mut ");
                } else {
                    self.write("let ");
                }
                self.write(&name.name);

                // Type annotation (skip if it would cause a type mismatch with the init)
                if let Some(ty) = ty
                    && !skip_type_annotation
                {
                    self.write(&format!(": {}", Self::rust_type(ty)));
                }

                self.write(" = ");
                if let Some(init) = init {
                    // Set type hint from declared type for wrapping suffix inference
                    let old_hint = self.type_hint.take();
                    if let Some(ty) = ty {
                        let rust_ty = Self::rust_type(ty);
                        self.type_hint = Some(rust_ty);
                    }

                    // If the declared type is a slice/ref and the init is an array/hex/bytes
                    // literal, we need to add & to create a reference
                    let needs_ref = if let Some(ty) = ty {
                        Self::type_is_slice_or_ref(ty) && Self::expr_is_array_literal(init)
                    } else {
                        false
                    };
                    // Also need & when the init is a slice expression (produces unsized [T])
                    let needs_slice_ref = matches!(&init.kind, ExprKind::Slice { .. });
                    if needs_ref || needs_slice_ref {
                        self.write("&");
                    }
                    self.generate_expr(init);
                    self.type_hint = old_hint;
                } else if let Some(ty) = ty {
                    self.write(&Self::default_value_for_type(ty));
                } else {
                    self.write("Default::default()");
                }
                self.write(";\n");
            }
            StmtKind::Expr(expr) => {
                self.write_indent();
                self.generate_expr(expr);
                self.write(";\n");
            }
            StmtKind::Assign { target, value } => {
                // Check for endian cast assignment: buf[0..4] as u32be = value
                if let ExprKind::Cast { expr: inner, ty } = &target.kind
                    && let crate::parser::TypeKind::Primitive(p) = &ty.kind
                {
                    let endian = p.endianness();
                    if endian != crate::parser::Endianness::Native
                        && let ExprKind::Slice {
                            array, start, end, ..
                        } = &inner.kind
                    {
                        self.generate_endian_write_to_slice(array, start, end, p, value);
                        return;
                    }
                }

                self.write_indent();
                self.generate_expr(target);
                self.write(" = ");
                self.generate_expr(value);
                self.write(";\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                // For wrapping arithmetic, we need to expand compound assignments
                match op {
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul => {
                        // Infer the target type for proper literal suffixes
                        let suffix = self.infer_wrapping_suffix(target, value);
                        self.write_indent();
                        self.generate_expr(target);
                        self.write(" = ");
                        self.generate_typed_expr(target, &suffix);
                        let method = match op {
                            BinaryOp::Add => ".wrapping_add(",
                            BinaryOp::Sub => ".wrapping_sub(",
                            BinaryOp::Mul => ".wrapping_mul(",
                            _ => unreachable!(),
                        };
                        self.write(method);
                        self.generate_typed_expr(value, &suffix);
                        self.write(");\n");
                    }
                    BinaryOp::Shl => {
                        self.write_indent();
                        self.generate_expr(target);
                        self.write(" = ");
                        self.generate_expr(target);
                        self.write(".wrapping_shl(");
                        self.generate_expr(value);
                        self.write(" as u32);\n");
                    }
                    BinaryOp::Shr => {
                        self.write_indent();
                        self.generate_expr(target);
                        self.write(" = ");
                        self.generate_expr(target);
                        self.write(".wrapping_shr(");
                        self.generate_expr(value);
                        self.write(" as u32);\n");
                    }
                    _ => {
                        self.write_indent();
                        self.generate_expr(target);
                        let op_str = match op {
                            BinaryOp::Div => " /= ",
                            BinaryOp::Rem => " %= ",
                            BinaryOp::BitAnd => " &= ",
                            BinaryOp::BitOr => " |= ",
                            BinaryOp::BitXor => " ^= ",
                            _ => " = ",
                        };
                        self.write(op_str);
                        self.generate_expr(value);
                        self.write(";\n");
                    }
                }
            }
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.write_indent();
                self.write("if ");
                self.generate_expr(condition);
                self.write(" {\n");
                self.indent();
                self.generate_block(then_block);
                self.dedent();
                if let Some(else_block) = else_block {
                    self.writeln("} else {");
                    self.indent();
                    self.generate_block(else_block);
                    self.dedent();
                }
                self.writeln("}");
            }
            StmtKind::For {
                var,
                start,
                end,
                inclusive,
                body,
            } => {
                // Track the loop variable as u64 (consistent with AlgoC semantics)
                self.var_rust_types
                    .insert(var.name.clone(), "u64".to_string());

                self.write_indent();
                self.write(&format!("for {} in ", var.name));
                // Add type suffix to integer literal bounds to avoid ambiguous type
                self.generate_typed_expr(start, "u64");
                if *inclusive {
                    self.write("..=");
                } else {
                    self.write("..");
                }
                self.generate_typed_expr(end, "u64");
                self.write(" {\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::While { condition, body } => {
                self.write_indent();
                self.write("while ");
                self.generate_expr(condition);
                self.write(" {\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::Loop { body } => {
                self.writeln("loop {");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::Break => {
                self.writeln("break;");
            }
            StmtKind::Continue => {
                self.writeln("continue;");
            }
            StmtKind::Return(expr) => {
                self.write_indent();
                self.write("return");
                if let Some(expr) = expr {
                    self.write(" ");
                    self.generate_expr(expr);
                }
                self.write(";\n");
            }
            StmtKind::Block(block) => {
                self.writeln("{");
                self.indent();
                self.generate_block(block);
                self.dedent();
                self.writeln("}");
            }
        }
    }

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                self.write(&format!("{}", n));
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // Convert string to byte slice/Vec<u8>
                self.write(&format!("b\"{}\"", escape_rust_string(s)));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("b\"{}\"", escape_rust_string(s)));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to array literal
                let bytes: Vec<String> = (0..h.len())
                    .step_by(2)
                    .map(|i| {
                        if i + 2 <= h.len() {
                            format!("0x{}", &h[i..i + 2])
                        } else {
                            format!("0x0{}", &h[i..i + 1])
                        }
                    })
                    .collect();
                self.write(&format!("[{}]", bytes.join(", ")));
            }
            ExprKind::Ident(ident) => {
                // Rename 'self' to 'self_' to avoid keyword conflict
                if ident.name == "self" {
                    self.write("self_");
                } else {
                    self.write(&ident.name);
                }
            }
            ExprKind::Binary { left, op, right } => {
                // For array comparisons, use slice comparison
                if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
                    let left_is_array = is_array_like_expr(left);
                    let right_is_array = is_array_like_expr(right);

                    if left_is_array || right_is_array {
                        if matches!(op, BinaryOp::Ne) {
                            self.write("!");
                        }
                        self.write("constant_time_eq(");
                        self.generate_slice_ref(left);
                        self.write(", ");
                        self.generate_slice_ref(right);
                        self.write(")");
                        return;
                    }
                }

                match op {
                    // Wrapping arithmetic
                    BinaryOp::Add => {
                        let suffix = self.infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, &suffix);
                        self.write(".wrapping_add(");
                        self.generate_typed_expr(right, &suffix);
                        self.write(")");
                    }
                    BinaryOp::Sub => {
                        let suffix = self.infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, &suffix);
                        self.write(".wrapping_sub(");
                        self.generate_typed_expr(right, &suffix);
                        self.write(")");
                    }
                    BinaryOp::Mul => {
                        let suffix = self.infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, &suffix);
                        self.write(".wrapping_mul(");
                        self.generate_typed_expr(right, &suffix);
                        self.write(")");
                    }
                    BinaryOp::Shl => {
                        let suffix = self.infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, &suffix);
                        self.write(".wrapping_shl(");
                        self.generate_expr(right);
                        self.write(" as u32)");
                    }
                    BinaryOp::Shr => {
                        let suffix = self.infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, &suffix);
                        self.write(".wrapping_shr(");
                        self.generate_expr(right);
                        self.write(" as u32)");
                    }
                    // All other binary ops use standard operators
                    _ => {
                        self.write("(");
                        self.generate_expr(left);
                        let op_str = match op {
                            BinaryOp::Div => " / ",
                            BinaryOp::Rem => " % ",
                            BinaryOp::BitAnd => " & ",
                            BinaryOp::BitOr => " | ",
                            BinaryOp::BitXor => " ^ ",
                            BinaryOp::Eq => " == ",
                            BinaryOp::Ne => " != ",
                            BinaryOp::Lt => " < ",
                            BinaryOp::Le => " <= ",
                            BinaryOp::Gt => " > ",
                            BinaryOp::Ge => " >= ",
                            BinaryOp::And => " && ",
                            BinaryOp::Or => " || ",
                            _ => unreachable!(),
                        };
                        self.write(op_str);
                        self.generate_expr(right);
                        self.write(")");
                    }
                }
            }
            ExprKind::Unary { op, operand } => {
                let op_str = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                    UnaryOp::BitNot => "!",
                };
                self.write(op_str);
                self.write("(");
                self.generate_expr(operand);
                self.write(")");
            }
            ExprKind::Index { array, index } => {
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(index);
                self.write(" as usize]");
            }
            ExprKind::Slice {
                array,
                start,
                end,
                inclusive,
            } => {
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(start);
                self.write(" as usize..");
                if *inclusive {
                    self.write("=");
                }
                self.generate_expr(end);
                self.write(" as usize]");
            }
            ExprKind::Field { object, field } => {
                self.generate_expr(object);
                self.write(&format!(".{}", field.name));
            }
            ExprKind::Call { func, args } => {
                // Check for Reader/Writer constructor calls
                if let ExprKind::Ident(ident) = &func.kind
                    && (ident.name == "Reader" || ident.name == "Writer")
                {
                    self.write(&format!("{}::new(", ident.name));
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(arg);
                        // Reader/Writer::new takes Vec<u8>, but the argument may be &[u8]
                        // Add .to_vec() to convert
                        self.write(".to_vec()");
                    }
                    self.write(")");
                    return;
                }

                // Check for method calls like slice.len() or reader.read_u32()
                if let ExprKind::Field { object, field } = &func.kind {
                    if field.name == "len" && args.is_empty() {
                        self.write("(");
                        self.generate_expr(object);
                        self.write(".len() as u64)");
                        return;
                    }

                    // Handle reader.read(&mut struct) - expand to field reads
                    if field.name == "read"
                        && args.len() == 1
                        && let ExprKind::MutRef(inner) = &args[0].kind
                        && let ExprKind::Ident(var_ident) = &inner.kind
                        && let Some(struct_name) = self.var_types.get(&var_ident.name).cloned()
                        && let Some(fields) = self.struct_defs.get(&struct_name).cloned()
                    {
                        self.write("{ ");
                        for field_info in &fields {
                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty)
                            {
                                self.write(&format!("{}.{} = ", var_ident.name, field_info.name));
                                self.generate_expr(object);
                                self.write(&format!(".{}(); ", read_method));
                            }
                        }
                        self.write("}");
                        return;
                    }

                    // Handle writer.write(&struct) - expand to field writes
                    if field.name == "write" && args.len() == 1 {
                        let inner_expr = match &args[0].kind {
                            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => Some(inner.as_ref()),
                            _ => None,
                        };
                        if let Some(inner) = inner_expr
                            && let ExprKind::Ident(var_ident) = &inner.kind
                            && let Some(struct_name) = self.var_types.get(&var_ident.name).cloned()
                            && let Some(fields) = self.struct_defs.get(&struct_name).cloned()
                        {
                            self.write("{ ");
                            for field_info in &fields {
                                if let Some(write_method) =
                                    self.get_write_method_for_type(&field_info.ty)
                                {
                                    self.generate_expr(object);
                                    self.write(&format!(
                                        ".{}({}.{}); ",
                                        write_method, var_ident.name, field_info.name
                                    ));
                                }
                            }
                            self.write("}");
                            return;
                        }
                    }

                    // Reader/Writer method calls - pass through directly
                    let reader_writer_methods = [
                        "read_u8",
                        "read_u16",
                        "read_u16be",
                        "read_u16le",
                        "read_u32",
                        "read_u32be",
                        "read_u32le",
                        "read_u64",
                        "read_u64be",
                        "read_u64le",
                        "read_bytes",
                        "read_chunk",
                        "eof",
                        "write_u8",
                        "write_u16",
                        "write_u16be",
                        "write_u16le",
                        "write_u32",
                        "write_u32be",
                        "write_u32le",
                        "write_u64",
                        "write_u64be",
                        "write_u64le",
                        "write_bytes",
                    ];
                    if reader_writer_methods.contains(&field.name.as_str()) {
                        self.generate_expr(object);
                        self.write(&format!(".{}(", field.name));
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            // For read_bytes/read_chunk, cast count to usize
                            if (field.name == "read_bytes" || field.name == "read_chunk") && i == 0
                            {
                                self.generate_expr(arg);
                                self.write(" as usize");
                            } else if field.name == "write_bytes" && i == 0 {
                                // write_bytes needs a slice reference
                                self.write("&");
                                self.generate_expr(arg);
                            } else {
                                self.generate_expr(arg);
                            }
                        }
                        self.write(")");
                        return;
                    }

                    // Check for struct method calls (object.method(args))
                    if let ExprKind::Ident(obj_ident) = &object.kind {
                        let obj_name = if obj_ident.name == "self" {
                            "self_"
                        } else {
                            &obj_ident.name
                        };
                        if let Some(struct_name) = self.var_types.get(obj_name).cloned()
                            && let Some(methods) = self.struct_methods.get(&struct_name).cloned()
                            && let Some(mangled_name) = methods.get(&field.name)
                        {
                            self.write(&format!("{}(", mangled_name));
                            self.generate_expr(object);
                            for arg in args {
                                self.write(", ");
                                self.generate_expr(arg);
                            }
                            self.write(")");
                            return;
                        }
                    }

                    // Handle rotate_left and rotate_right as native Rust methods
                    if field.name == "rotate_left" || field.name == "rotate_right" {
                        self.generate_expr(object);
                        self.write(&format!(".{}(", field.name));
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_expr(arg);
                            self.write(" as u32");
                        }
                        self.write(")");
                        return;
                    }

                    // Handle wrapping_add, wrapping_sub, etc. as native methods
                    if field.name.starts_with("wrapping_")
                        || field.name.starts_with("to_")
                        || field.name.starts_with("from_")
                    {
                        self.generate_expr(object);
                        self.write(&format!(".{}(", field.name));
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_expr(arg);
                        }
                        self.write(")");
                        return;
                    }

                    // Handle clone() method
                    if field.name == "clone" && args.is_empty() {
                        self.generate_expr(object);
                        self.write(".clone()");
                        return;
                    }

                    // Handle to_vec() method
                    if field.name == "to_vec" && args.is_empty() {
                        self.generate_expr(object);
                        self.write(".to_vec()");
                        return;
                    }

                    // Handle copy_from_slice
                    if field.name == "copy_from_slice" {
                        self.generate_expr(object);
                        self.write(".copy_from_slice(");
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_expr(arg);
                        }
                        self.write(")");
                        return;
                    }
                }

                // Regular function call
                self.generate_expr(func);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    // Auto-borrow Vec arguments that will be passed to slice parameters
                    if self.arg_needs_borrow(arg) {
                        self.write("&");
                    }
                    self.generate_expr(arg);
                }
                self.write(")");
            }
            ExprKind::Builtin { name, args } => {
                self.generate_builtin(*name, args);
            }
            ExprKind::Array(elements) => {
                self.write("[");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_expr(elem);
                }
                self.write("]");
            }
            ExprKind::ArrayRepeat { value, count } => {
                // Check if count is a compile-time constant
                let count_is_const = matches!(count.kind, ExprKind::Integer(_));
                if count_is_const {
                    self.write("[");
                    self.generate_expr(value);
                    self.write("; ");
                    self.generate_expr(count);
                    self.write("]");
                } else {
                    self.write("vec![");
                    self.generate_expr(value);
                    self.write("; ");
                    self.generate_expr(count);
                    self.write(" as usize]");
                }
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) => {
                self.write("&");
                self.generate_expr(inner);
            }
            ExprKind::MutRef(inner) => {
                self.write("&mut ");
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                self.write("*");
                self.generate_expr(inner);
            }
            ExprKind::Range {
                start,
                end,
                inclusive,
            } => {
                self.generate_expr(start);
                if *inclusive {
                    self.write("..=");
                } else {
                    self.write("..");
                }
                self.generate_expr(end);
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.generate_expr(inner);
                self.write(")");
            }
            ExprKind::StructLit { name, fields } => {
                self.write(&format!("{} {{ ", name.name));
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("{}: ", field_name.name));
                    self.generate_expr(value);
                }
                self.write(" }");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                self.write("if ");
                self.generate_expr(condition);
                self.write(" { ");
                self.generate_expr(then_expr);
                self.write(" } else { ");
                self.generate_expr(else_expr);
                self.write(" }");
            }
            ExprKind::EnumVariant {
                enum_name,
                variant_name,
                args,
            } => {
                if args.is_empty() {
                    self.write(&format!("{}::{}", enum_name.name, variant_name.name));
                } else {
                    self.write(&format!("{}::{}(", enum_name.name, variant_name.name));
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(arg);
                    }
                    self.write(")");
                }
            }
            ExprKind::Match { expr, arms } => {
                self.write("match ");
                self.generate_expr(expr);
                self.write(" {\n");
                self.indent();
                for arm in arms {
                    self.write_indent();
                    self.generate_pattern(&arm.pattern);
                    self.write(" => ");
                    self.generate_expr(&arm.body);
                    self.write(",\n");
                }
                self.dedent();
                self.write_indent();
                self.write("}");
            }
            ExprKind::MethodCall {
                receiver,
                mangled_name,
                args,
                ..
            } => {
                // Generate: mangled_name(receiver, args...)
                self.write(&format!("{}(", mangled_name));
                self.generate_expr(receiver);
                for arg in args {
                    self.write(", ");
                    self.generate_expr(arg);
                }
                self.write(")");
            }
            ExprKind::TypeStaticCall {
                type_name,
                method_name,
                args,
            } => {
                // Should be resolved by monomorphization
                self.write(&format!("{}__{}", type_name.name, method_name.name));
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_expr(arg);
                }
                self.write(")");
            }
            ExprKind::GenericCall { func, args, .. } => {
                // Should be resolved by monomorphization - generate as regular call
                self.generate_expr(func);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_expr(arg);
                }
                self.write(")");
            }
        }
    }

    fn generate_pattern(&mut self, pattern: &crate::parser::Pattern) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("_");
            }
            PatternKind::Literal(lit_expr) => {
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(ident) => {
                self.write(&ident.name);
            }
            PatternKind::EnumVariant {
                enum_name,
                variant_name,
                bindings,
            } => {
                self.write(&format!("{}::{}", enum_name.name, variant_name.name));
                if !bindings.is_empty() {
                    self.write("(");
                    for (i, binding) in bindings.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_pattern(binding);
                    }
                    self.write(")");
                }
            }
            PatternKind::Tuple(patterns) => {
                self.write("(");
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_pattern(p);
                }
                self.write(")");
            }
            PatternKind::Or(patterns) => {
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" | ");
                    }
                    self.generate_pattern(p);
                }
            }
        }
    }

    fn generate_builtin(&mut self, name: BuiltinFunc, args: &[Expr]) {
        match name {
            BuiltinFunc::Assert => {
                self.write("__assert(");
                self.generate_expr(&args[0]);
                self.write(")");
            }
        }
    }

    fn generate_cast(&mut self, expr: &Expr, ty: &crate::parser::Type) {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        // Check for endian byte conversions (byte slice/array to integer)
        if let TypeKind::Primitive(p) = &ty.kind {
            let endian = p.endianness();
            if endian != Endianness::Native {
                let native = p.to_native();

                // Check if source is a slice/array (byte conversion)
                if is_byte_sequence_expr(expr) {
                    self.generate_from_bytes(expr, native, endian);
                    return;
                }

                // Integer to integer with different endianness - just cast to native type
                let rust_ty = Self::rust_native_type(native);
                self.write("(");
                self.generate_expr(expr);
                self.write(&format!(" as {})", rust_ty));
                return;
            }
        }

        // Check for integer to byte array cast
        if let TypeKind::Array { element, size: _ } = &ty.kind
            && let TypeKind::Primitive(PrimitiveType::U8) = &element.kind
        {
            let (endian, bits) = self.get_expr_endianness_info(expr);
            self.generate_to_bytes(expr, endian, bits);
            return;
        }

        // Standard casts
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let rust_ty = Self::rust_native_type(p.to_native());
                self.write("(");
                self.generate_expr(expr);
                self.write(&format!(" as {})", rust_ty));
            }
            TypeKind::Slice { element } => {
                // Cast to slice - use as_slice or borrow
                let _elem_ty = Self::rust_type(element);
                self.write("&");
                self.generate_expr(expr);
                self.write("[..]");
            }
            _ => {
                // For other types, just generate the expression
                self.generate_expr(expr);
            }
        }
    }

    /// Generate code for reading bytes as an integer (e.g., buf[0..4] as u32be)
    fn generate_from_bytes(
        &mut self,
        expr: &Expr,
        native: crate::parser::PrimitiveType,
        endian: crate::parser::Endianness,
    ) {
        use crate::parser::PrimitiveType;

        let rust_ty = Self::rust_native_type(native);
        let byte_method = match endian {
            crate::parser::Endianness::Big => "from_be_bytes",
            crate::parser::Endianness::Little => "from_le_bytes",
            crate::parser::Endianness::Native => "from_ne_bytes",
        };

        let byte_count = match native {
            PrimitiveType::U8 | PrimitiveType::I8 => 1,
            PrimitiveType::U16 | PrimitiveType::I16 => 2,
            PrimitiveType::U32 | PrimitiveType::I32 => 4,
            PrimitiveType::U64 | PrimitiveType::I64 => 8,
            PrimitiveType::U128 | PrimitiveType::I128 => 16,
            _ => 4,
        };

        if byte_count == 1 {
            // Single byte - just index
            self.generate_expr(expr);
            self.write("[0]");
        } else {
            // Use from_xx_bytes with a try_into for the array conversion
            // Note: we generate expr directly (not as a slice ref) because from_xx_bytes
            // takes an owned [u8; N], and try_into() on a slice produces the right type.
            self.write(&format!("{}::{}(", rust_ty, byte_method));
            self.generate_expr(expr);
            self.write(&format!("[..{}].try_into().unwrap())", byte_count));
        }
    }

    /// Generate code for converting an integer to bytes (e.g., value as u8[4])
    fn generate_to_bytes(&mut self, expr: &Expr, endian: crate::parser::Endianness, bits: u32) {
        let byte_method = match endian {
            crate::parser::Endianness::Big => "to_be_bytes",
            crate::parser::Endianness::Little => "to_le_bytes",
            crate::parser::Endianness::Native => "to_ne_bytes",
        };

        // Strip the inner endian cast if present to get at the raw value
        let inner = if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
            inner.as_ref()
        } else {
            expr
        };

        let cast_ty = match bits {
            16 => "u16",
            32 => "u32",
            64 => "u64",
            128 => "u128",
            _ => "u32",
        };

        self.write("(");
        self.generate_expr(inner);
        self.write(&format!(" as {}).{}().to_vec()", cast_ty, byte_method));
    }

    /// Generate endian write to a slice (e.g., buf[0..4] as u32be = value)
    fn generate_endian_write_to_slice(
        &mut self,
        array: &Expr,
        start: &Expr,
        end: &Expr,
        prim: &crate::parser::PrimitiveType,
        value: &Expr,
    ) {
        let endian = prim.endianness();
        let native = prim.to_native();

        let byte_method = match endian {
            crate::parser::Endianness::Big => "to_be_bytes",
            crate::parser::Endianness::Little => "to_le_bytes",
            crate::parser::Endianness::Native => "to_ne_bytes",
        };

        let cast_ty = Self::rust_native_type(native);

        self.write_indent();
        self.generate_expr(array);
        self.write("[");
        self.generate_expr(start);
        self.write(" as usize..");
        self.generate_expr(end);
        self.write(" as usize].copy_from_slice(&(");
        self.generate_expr(value);
        self.write(&format!(" as {}).{}());\n", cast_ty, byte_method));
    }

    /// Generate a reference to a slice (&[u8])
    fn generate_slice_ref(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Slice {
                array,
                start,
                end,
                inclusive,
            } => {
                self.write("&");
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(start);
                self.write(" as usize..");
                if *inclusive {
                    self.write("=");
                }
                self.generate_expr(end);
                self.write(" as usize]");
            }
            ExprKind::Hex(_) | ExprKind::Bytes(_) | ExprKind::String(_) => {
                self.write("&");
                self.generate_expr(expr);
            }
            ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } => {
                self.write("&");
                self.generate_expr(expr);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                self.write("&");
                self.generate_expr(inner);
            }
            _ => {
                self.write("&");
                self.generate_expr(expr);
            }
        }
    }

    /// Get endianness info from an expression (endianness, bits)
    fn get_expr_endianness_info(&self, expr: &Expr) -> (crate::parser::Endianness, u32) {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        if let ExprKind::Cast { ty, .. } = &expr.kind
            && let TypeKind::Primitive(p) = &ty.kind
        {
            let endian = p.endianness();
            let bits = match p.to_native() {
                PrimitiveType::U16 | PrimitiveType::I16 => 16,
                PrimitiveType::U32 | PrimitiveType::I32 => 32,
                PrimitiveType::U64 | PrimitiveType::I64 => 64,
                PrimitiveType::U128 | PrimitiveType::I128 => 128,
                _ => 32,
            };
            return (endian, bits);
        }
        // Default to little endian, 32 bits
        (Endianness::Little, 32)
    }

    /// Get the Reader method name for reading a field type
    fn get_read_method_for_type(&self, ty: &ParserType) -> Option<String> {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        match &ty.kind {
            TypeKind::Primitive(p) => {
                let endian = p.endianness();
                let native = p.to_native();
                let suffix = match endian {
                    Endianness::Big => "be",
                    Endianness::Little => "le",
                    Endianness::Native => "be", // Default to big-endian
                };
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => Some("read_u8".to_string()),
                    PrimitiveType::U16 | PrimitiveType::I16 => Some(format!("read_u16{}", suffix)),
                    PrimitiveType::U32 | PrimitiveType::I32 => Some(format!("read_u32{}", suffix)),
                    PrimitiveType::U64 | PrimitiveType::I64 => Some(format!("read_u64{}", suffix)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Get the Writer method name for writing a field type
    fn get_write_method_for_type(&self, ty: &ParserType) -> Option<String> {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        match &ty.kind {
            TypeKind::Primitive(p) => {
                let endian = p.endianness();
                let native = p.to_native();
                let suffix = match endian {
                    Endianness::Big => "be",
                    Endianness::Little => "le",
                    Endianness::Native => "be", // Default to big-endian
                };
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => Some("write_u8".to_string()),
                    PrimitiveType::U16 | PrimitiveType::I16 => Some(format!("write_u16{}", suffix)),
                    PrimitiveType::U32 | PrimitiveType::I32 => Some(format!("write_u32{}", suffix)),
                    PrimitiveType::U64 | PrimitiveType::I64 => Some(format!("write_u64{}", suffix)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Convert a parser type to a Rust type string
    fn rust_type(ty: &crate::parser::Type) -> String {
        Self::rust_type_replacing_self(ty, None)
    }

    /// Convert a parser type to a Rust type string, optionally replacing `Self` with a concrete name
    fn rust_type_replacing_self(ty: &crate::parser::Type, self_name: Option<&str>) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => Self::rust_native_type(p.to_native()),
            TypeKind::Array { element, size } => {
                format!(
                    "[{}; {}]",
                    Self::rust_type_replacing_self(element, self_name),
                    size
                )
            }
            TypeKind::Slice { element } => {
                format!("&[{}]", Self::rust_type_replacing_self(element, self_name))
            }
            TypeKind::ArrayRef { element, size } => {
                format!(
                    "&[{}; {}]",
                    Self::rust_type_replacing_self(element, self_name),
                    size
                )
            }
            TypeKind::MutRef(inner) => {
                // Handle MutRef(Slice(T)) => &mut [T] (not &mut &[T])
                if let TypeKind::Slice { element } = &inner.kind {
                    format!(
                        "&mut [{}]",
                        Self::rust_type_replacing_self(element, self_name)
                    )
                } else {
                    format!("&mut {}", Self::rust_type_replacing_self(inner, self_name))
                }
            }
            TypeKind::Ref(inner) => {
                // Handle Ref(Slice(T)) => &[T] (not &&[T])
                if let TypeKind::Slice { element } = &inner.kind {
                    format!("&[{}]", Self::rust_type_replacing_self(element, self_name))
                } else {
                    format!("&{}", Self::rust_type_replacing_self(inner, self_name))
                }
            }
            TypeKind::Named(ident) => {
                // Handle Named("Self") the same as SelfType
                if ident.name == "Self" {
                    if let Some(name) = self_name {
                        name.to_string()
                    } else {
                        "Self".to_string()
                    }
                } else {
                    ident.name.clone()
                }
            }
            TypeKind::SelfType => {
                if let Some(name) = self_name {
                    name.to_string()
                } else {
                    "Self".to_string()
                }
            }
        }
    }

    /// Try to infer a Rust integer type suffix from an expression.
    /// Returns a suffix like "u32", "u64", or "" if unknown.
    fn infer_int_type_suffix(expr: &Expr) -> &'static str {
        match &expr.kind {
            ExprKind::Cast { ty, .. } => {
                if let crate::parser::TypeKind::Primitive(p) = &ty.kind {
                    match p.to_native() {
                        crate::parser::PrimitiveType::U8 => "u8",
                        crate::parser::PrimitiveType::U16 => "u16",
                        crate::parser::PrimitiveType::U32 => "u32",
                        crate::parser::PrimitiveType::U64 => "u64",
                        crate::parser::PrimitiveType::U128 => "u128",
                        crate::parser::PrimitiveType::I8 => "i8",
                        crate::parser::PrimitiveType::I16 => "i16",
                        crate::parser::PrimitiveType::I32 => "i32",
                        crate::parser::PrimitiveType::I64 => "i64",
                        crate::parser::PrimitiveType::I128 => "i128",
                        _ => "",
                    }
                } else {
                    ""
                }
            }
            ExprKind::Binary { left, right, .. } => {
                let l = Self::infer_int_type_suffix(left);
                if !l.is_empty() {
                    return l;
                }
                Self::infer_int_type_suffix(right)
            }
            ExprKind::Paren(inner) => Self::infer_int_type_suffix(inner),
            ExprKind::Unary { operand, .. } => Self::infer_int_type_suffix(operand),
            _ => "",
        }
    }

    /// Infer the Rust type of an expression from context (variable types, struct fields, etc.)
    /// Returns a type string like "u32", "u64", "u8", or empty string if unknown.
    fn infer_expr_rust_type(&self, expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Ident(ident) => {
                let name = if ident.name == "self" {
                    "self_"
                } else {
                    &ident.name
                };
                if let Some(ty) = self.var_rust_types.get(name) {
                    return ty.clone();
                }
                if let Some(ty) = self.param_rust_types.get(name) {
                    return ty.clone();
                }
                String::new()
            }
            ExprKind::Cast { ty, .. } => {
                if let crate::parser::TypeKind::Primitive(p) = &ty.kind {
                    return Self::rust_native_type(p.to_native());
                }
                String::new()
            }
            ExprKind::Field { object, field } => {
                // Determine the struct type of the object
                let struct_name = match &object.kind {
                    ExprKind::Ident(ident) => {
                        let name = if ident.name == "self" {
                            "self_"
                        } else {
                            &ident.name
                        };
                        self.var_types.get(name).cloned()
                    }
                    _ => None,
                };
                if let Some(sname) = struct_name
                    && let Some(fields) = self.struct_defs.get(&sname)
                {
                    for f in fields {
                        if f.name == field.name {
                            return Self::rust_type(&f.ty);
                        }
                    }
                }
                String::new()
            }
            ExprKind::Index { array, .. } => {
                // If we index into an array/slice, the result is the element type
                let array_type = self.infer_expr_rust_type(array);
                if let Some(stripped) = array_type.strip_prefix('[') {
                    // [u32; 8] -> u32
                    if let Some(semi_pos) = stripped.find(';') {
                        return stripped[..semi_pos].trim().to_string();
                    }
                }
                if let Some(stripped) = array_type.strip_prefix("&[") {
                    // &[u8] -> u8
                    if let Some(end) = stripped.strip_suffix(']') {
                        return end.trim().to_string();
                    }
                }
                if let Some(stripped) = array_type.strip_prefix("&mut [")
                    && let Some(end) = stripped.strip_suffix(']')
                {
                    return end.trim().to_string();
                }
                String::new()
            }
            ExprKind::Binary { left, right, .. } => {
                let lt = self.infer_expr_rust_type(left);
                if !lt.is_empty() {
                    return lt;
                }
                self.infer_expr_rust_type(right)
            }
            ExprKind::Paren(inner) => self.infer_expr_rust_type(inner),
            ExprKind::Unary { operand, .. } => self.infer_expr_rust_type(operand),
            ExprKind::Call { func, args } => {
                // .len() returns u64
                if let ExprKind::Field { field, .. } = &func.kind
                    && field.name == "len"
                    && args.is_empty()
                {
                    return "u64".to_string();
                }
                String::new()
            }
            _ => String::new(),
        }
    }

    /// Determine the type suffix needed for wrapping operations.
    /// If either operand is an integer literal, we need a suffix to avoid ambiguity.
    /// Returns the suffix to apply to integer literals (empty string if no literals present).
    fn infer_wrapping_suffix(&self, left: &Expr, right: &Expr) -> String {
        let left_is_lit = matches!(left.kind, ExprKind::Integer(_));
        let right_is_lit = matches!(right.kind, ExprKind::Integer(_));

        if !left_is_lit && !right_is_lit {
            // Neither side is a literal, no suffix needed
            return String::new();
        }

        // Use context type hint first if available (e.g., from let binding).
        // This takes priority because the declared type of the variable is the
        // most authoritative source of what type the expression should produce.
        if let Some(ref hint) = self.type_hint
            && Self::is_rust_int_type(hint)
        {
            return hint.clone();
        }

        // Try to infer from the non-literal side using static analysis
        if left_is_lit && !right_is_lit {
            let s = Self::infer_int_type_suffix(right);
            if !s.is_empty() {
                return s.to_string();
            }
            // Try runtime type inference
            let rt = self.infer_expr_rust_type(right);
            if !rt.is_empty() && Self::is_rust_int_type(&rt) {
                return rt;
            }
        }
        if right_is_lit && !left_is_lit {
            let s = Self::infer_int_type_suffix(left);
            if !s.is_empty() {
                return s.to_string();
            }
            let lt = self.infer_expr_rust_type(left);
            if !lt.is_empty() && Self::is_rust_int_type(&lt) {
                return lt;
            }
        }

        // Both are literals or we couldn't infer - default to u64
        // (most common integer type in crypto code)
        "u64".to_string()
    }

    /// Check if a string is a Rust integer type
    fn is_rust_int_type(ty: &str) -> bool {
        matches!(
            ty,
            "u8" | "u16" | "u32" | "u64" | "u128" | "i8" | "i16" | "i32" | "i64" | "i128"
        )
    }

    /// Generate an integer literal with an explicit type suffix if needed.
    /// `suffix` is the type suffix to add (e.g., "u32", "u64").
    fn generate_typed_expr(&mut self, expr: &Expr, suffix: &str) {
        if let ExprKind::Integer(n) = &expr.kind {
            if !suffix.is_empty() {
                self.write(&format!("{}{}", n, suffix));
            } else {
                self.write(&format!("{}", n));
            }
        } else {
            self.generate_expr(expr);
        }
    }

    /// Infer the concrete type name that should replace `Self` in a function.
    /// For functions with names like "StructName__method", the prefix is the struct name.
    /// Also checks if any parameter or return type actually uses SelfType.
    fn infer_self_type_name(func_name: &str, func: &Function) -> Option<String> {
        // Check if any type in the function signature uses SelfType
        let has_self_type = func.params.iter().any(|p| Self::type_contains_self(&p.ty))
            || func
                .return_type
                .as_ref()
                .is_some_and(Self::type_contains_self);

        if !has_self_type {
            return None;
        }

        // Try to extract struct name from mangled function name (e.g., "Sha256State__update")
        if let Some(idx) = func_name.find("__") {
            return Some(func_name[..idx].to_string());
        }

        None
    }

    /// Convert a parser type to a Rust parameter type string.
    /// For function parameters, array refs (&[T; N]) are converted to slices (&[T])
    /// and &mut [T; N] is converted to &mut [T] for more flexible function signatures.
    fn rust_param_type(ty: &crate::parser::Type, self_name: Option<&str>) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::ArrayRef { element, .. } => {
                format!("&[{}]", Self::rust_type_replacing_self(element, self_name))
            }
            TypeKind::Ref(inner) => {
                if let TypeKind::Array { element, .. } = &inner.kind {
                    format!("&[{}]", Self::rust_type_replacing_self(element, self_name))
                } else if let TypeKind::Slice { element } = &inner.kind {
                    format!("&[{}]", Self::rust_type_replacing_self(element, self_name))
                } else {
                    Self::rust_type_replacing_self(ty, self_name)
                }
            }
            TypeKind::MutRef(inner) => {
                if let TypeKind::Slice { element } = &inner.kind {
                    format!(
                        "&mut [{}]",
                        Self::rust_type_replacing_self(element, self_name)
                    )
                } else if let TypeKind::ArrayRef { element, .. } = &inner.kind {
                    format!(
                        "&mut [{}]",
                        Self::rust_type_replacing_self(element, self_name)
                    )
                } else if let TypeKind::Array { element, .. } = &inner.kind {
                    format!(
                        "&mut [{}]",
                        Self::rust_type_replacing_self(element, self_name)
                    )
                } else {
                    Self::rust_type_replacing_self(ty, self_name)
                }
            }
            _ => Self::rust_type_replacing_self(ty, self_name),
        }
    }

    /// Check if a type contains SelfType anywhere (either TypeKind::SelfType or Named("Self"))
    fn type_contains_self(ty: &crate::parser::Type) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::SelfType => true,
            TypeKind::Named(ident) if ident.name == "Self" => true,
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => Self::type_contains_self(inner),
            TypeKind::Array { element, .. }
            | TypeKind::Slice { element }
            | TypeKind::ArrayRef { element, .. } => Self::type_contains_self(element),
            _ => false,
        }
    }

    /// Check if a type is a slice or reference type (e.g., &[u8], &T)
    fn type_is_slice_or_ref(ty: &crate::parser::Type) -> bool {
        use crate::parser::TypeKind;
        matches!(
            &ty.kind,
            TypeKind::Slice { .. } | TypeKind::Ref(_) | TypeKind::ArrayRef { .. }
        )
    }

    /// Check if an expression is an array/hex/bytes literal that would need & to become a reference
    fn expr_is_array_literal(expr: &Expr) -> bool {
        matches!(
            &expr.kind,
            ExprKind::Hex(_) | ExprKind::Array(_) | ExprKind::ArrayRepeat { .. }
        )
    }

    /// Check if a function argument needs auto-borrowing.
    /// This is needed when passing a Vec-typed variable to a function expecting a slice.
    fn arg_needs_borrow(&self, arg: &Expr) -> bool {
        if let ExprKind::Ident(ident) = &arg.kind
            && let Some(ty) = self.var_rust_types.get(&ident.name)
        {
            return ty.starts_with("Vec<");
        }
        false
    }

    /// Check if an expression returns a Vec (e.g., reader.read_chunk, reader.read_bytes)
    /// These can't be assigned to &[u8] directly - the type annotation must be skipped.
    fn expr_returns_vec(expr: &Expr) -> bool {
        if let ExprKind::Call { func, .. } = &expr.kind
            && let ExprKind::Field { field, .. } = &func.kind
        {
            return matches!(field.name.as_str(), "read_chunk" | "read_bytes" | "to_vec");
        }
        false
    }

    /// Check if a function needs lifetime annotations.
    /// This is needed when a function has a struct-with-lifetime parameter
    /// and also has reference parameters that could be stored in that struct.
    fn function_needs_lifetime(&self, func: &Function) -> bool {
        let has_struct_with_lifetime = func.params.iter().any(|p| {
            // Check if parameter is &mut SomeStruct where SomeStruct has lifetime fields
            match &p.ty.kind {
                crate::parser::TypeKind::MutRef(inner) => {
                    if let crate::parser::TypeKind::Named(ident) = &inner.kind {
                        // Check if this struct has any fields that need lifetimes
                        if let Some(fields) = self.struct_defs.get(&ident.name) {
                            return fields.iter().any(|f| Self::type_needs_lifetime(&f.ty));
                        }
                    }
                    false
                }
                _ => false,
            }
        });

        let has_ref_param = func.params.iter().any(|p| {
            matches!(
                &p.ty.kind,
                crate::parser::TypeKind::Slice { .. }
                    | crate::parser::TypeKind::Ref(_)
                    | crate::parser::TypeKind::ArrayRef { .. }
            ) || matches!(&p.ty.kind, crate::parser::TypeKind::MutRef(inner) if matches!(&inner.kind, crate::parser::TypeKind::Slice { .. }))
        });

        has_struct_with_lifetime && has_ref_param
    }

    /// Check if a type contains any references that need a lifetime annotation
    fn type_needs_lifetime(ty: &crate::parser::Type) -> bool {
        use crate::parser::TypeKind;
        matches!(
            &ty.kind,
            TypeKind::Slice { .. }
                | TypeKind::Ref(_)
                | TypeKind::MutRef(_)
                | TypeKind::ArrayRef { .. }
        )
    }

    /// Check if a type contains a mutable reference (which prevents deriving Clone)
    fn type_contains_mut_ref(ty: &crate::parser::Type) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::MutRef(_) => true,
            TypeKind::Array { element, .. } => Self::type_contains_mut_ref(element),
            _ => false,
        }
    }

    /// Convert a parser type to a Rust type string, adding lifetime 'a to references
    fn rust_type_with_lifetime(&self, ty: &crate::parser::Type) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Slice { element } => {
                format!("&'a [{}]", Self::rust_type(element))
            }
            TypeKind::Ref(inner) => {
                // Handle Ref(Slice(T)) => &'a [T]
                if let TypeKind::Slice { element } = &inner.kind {
                    format!("&'a [{}]", Self::rust_type(element))
                } else {
                    format!("&'a {}", self.rust_type_with_lifetime(inner))
                }
            }
            TypeKind::MutRef(inner) => {
                // Handle MutRef(Slice(T)) => &'a mut [T]
                if let TypeKind::Slice { element } = &inner.kind {
                    format!("&'a mut [{}]", Self::rust_type(element))
                } else {
                    format!("&'a mut {}", self.rust_type_with_lifetime(inner))
                }
            }
            TypeKind::ArrayRef { element, size } => {
                format!("&'a [{}; {}]", Self::rust_type(element), size)
            }
            TypeKind::Named(ident) => {
                // Check if this named type is a struct with lifetime fields
                if let Some(fields) = self.struct_defs.get(&ident.name)
                    && fields.iter().any(|f| Self::type_needs_lifetime(&f.ty))
                {
                    return format!("{}<'a>", ident.name);
                }
                ident.name.clone()
            }
            _ => Self::rust_type(ty),
        }
    }

    /// Convert a native primitive type to its Rust type name
    fn rust_native_type(p: crate::parser::PrimitiveType) -> String {
        use crate::parser::PrimitiveType;
        match p {
            PrimitiveType::U8 => "u8".to_string(),
            PrimitiveType::U16 => "u16".to_string(),
            PrimitiveType::U32 => "u32".to_string(),
            PrimitiveType::U64 => "u64".to_string(),
            PrimitiveType::U128 => "u128".to_string(),
            PrimitiveType::I8 => "i8".to_string(),
            PrimitiveType::I16 => "i16".to_string(),
            PrimitiveType::I32 => "i32".to_string(),
            PrimitiveType::I64 => "i64".to_string(),
            PrimitiveType::I128 => "i128".to_string(),
            PrimitiveType::Bool => "bool".to_string(),
            // Endian types map to their native equivalents
            _ => Self::rust_native_type(p.to_native()),
        }
    }
}

/// Check if an expression is likely an array type (used for comparison)
fn is_array_like_expr(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Hex(_) | ExprKind::Bytes(_) | ExprKind::String(_) => true,
        ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } => true,
        ExprKind::Slice { .. } => true,
        ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Deref(inner) => {
            is_array_like_expr(inner)
        }
        ExprKind::Paren(inner) => is_array_like_expr(inner),
        _ => false,
    }
}

/// Check if an expression produces a byte sequence (for from_bytes conversion)
fn is_byte_sequence_expr(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Slice { .. } => true,
        ExprKind::Hex(_) | ExprKind::Bytes(_) | ExprKind::String(_) => true,
        ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } => true,
        ExprKind::Index { .. } => false, // Single element
        ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Paren(inner) => {
            is_byte_sequence_expr(inner)
        }
        ExprKind::Ident(_) => true,
        ExprKind::Field { .. } => true,
        _ => false,
    }
}

impl Default for RustGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for RustGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();
        self.var_rust_types.clear();
        self.param_rust_types.clear();
        self.func_return_types.clear();

        // Pre-pass: collect struct definitions and method mappings
        for item in &ast.ast.items {
            match &item.kind {
                ItemKind::Struct(s) => {
                    let fields: Vec<StructFieldInfo> = s
                        .fields
                        .iter()
                        .map(|f| StructFieldInfo {
                            name: f.name.name.clone(),
                            ty: f.ty.clone(),
                        })
                        .collect();
                    self.struct_defs.insert(s.name.name.clone(), fields);
                }
                ItemKind::Layout(l) => {
                    let fields: Vec<StructFieldInfo> = l
                        .fields
                        .iter()
                        .map(|f| StructFieldInfo {
                            name: f.name.name.clone(),
                            ty: f.ty.clone(),
                        })
                        .collect();
                    self.struct_defs.insert(l.name.name.clone(), fields);
                }
                ItemKind::Impl(impl_def) => {
                    let mut methods = HashMap::new();
                    for method in &impl_def.methods {
                        let mangled = format!("{}__{}", impl_def.target.name, method.name.name);
                        methods.insert(method.name.name.clone(), mangled);
                    }
                    self.struct_methods
                        .insert(impl_def.target.name.clone(), methods);
                }
                _ => {}
            }
        }

        self.writeln(
            "#![allow(unused, non_snake_case, non_upper_case_globals, non_camel_case_types)]",
        );
        self.writeln("#![allow(arithmetic_overflow, overflowing_literals)]");
        self.writeln("");
        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("");
        self.writeln("use std::convert::TryInto;");
        self.writeln("");

        self.generate_runtime();

        if self.include_tests {
            self.generate_test_runtime();
        }

        self.generate_ast(&ast.ast);

        // Collect test names for the runner
        let test_names: Vec<_> = ast
            .ast
            .items
            .iter()
            .filter_map(|item| {
                if let ItemKind::Test(t) = &item.kind {
                    Some(t.name.name.clone())
                } else {
                    None
                }
            })
            .collect();

        // Generate main function with test runner if tests are included
        if self.include_tests {
            self.writeln("fn main() {");
            self.indent();
            self.writeln("let mut __passed: i32 = 0;");
            self.writeln("let mut __failed: i32 = 0;");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("unsafe {{ __TEST_NAME = \"{}\"; }}", name));
                self.writeln("unsafe { __TEST_FAILURES = 0; }");
                self.writeln(&format!(
                    "let __result = std::panic::catch_unwind(|| test_{}());",
                    name
                ));
                self.writeln("match __result {");
                self.indent();
                self.writeln("Ok(()) => {");
                self.indent();
                self.writeln("if unsafe { __TEST_FAILURES } == 0 {");
                self.indent();
                self.writeln(&format!("println!(\"PASS: {}\");", name));
                self.writeln("__passed += 1;");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("println!(\"FAIL: {}\");", name));
                self.writeln("__failed += 1;");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("}");
                self.writeln("Err(e) => {");
                self.indent();
                self.writeln(&format!("println!(\"FAIL: {} - {{:?}}\", e);", name));
                self.writeln("__failed += 1;");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("println!();");
            self.writeln("println!(\"{} passed, {} failed\", __passed, __failed);");
            self.writeln("if __failed > 0 {");
            self.indent();
            self.writeln("std::process::exit(1);");
            self.dedent();
            self.writeln("}");
            self.dedent();
            self.writeln("}");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "rs"
    }

    fn language_name(&self) -> &'static str {
        "Rust"
    }
}

fn escape_rust_string(s: &str) -> String {
    let mut result = String::new();
    for c in s.chars() {
        match c {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            _ => result.push(c),
        }
    }
    result
}
