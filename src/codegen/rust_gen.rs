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

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            // Handle self parameter
            if param.name.name == "self" {
                self.write(&format!("self_: {}", Self::rust_type(&param.ty)));
            } else {
                self.write(&format!(
                    "{}: {}",
                    param.name.name,
                    Self::rust_type(&param.ty)
                ));
            }
        }

        self.write(")");

        // Return type
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!(" -> {}", Self::rust_type(ret_ty)));
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
        self.writeln("#[derive(Clone)]");
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
                    Self::rust_type_with_lifetime(&field.ty)
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
        // Layouts are similar to structs in Rust
        self.writeln("#[derive(Clone)]");
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
                    Self::rust_type_with_lifetime(&field.ty)
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
        self.write_indent();
        self.write(&format!("fn {}(", func.name.name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            // Handle self parameter
            if param.name.name == "self" {
                self.write(&format!("self_: {}", Self::rust_type(&param.ty)));
            } else {
                self.write(&format!(
                    "{}: {}",
                    param.name.name,
                    Self::rust_type(&param.ty)
                ));
            }
        }

        self.write(")");

        // Return type
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!(" -> {}", Self::rust_type(ret_ty)));
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

                self.write_indent();
                if *mutable {
                    self.write("let mut ");
                } else {
                    self.write("let ");
                }
                self.write(&name.name);

                // Type annotation
                if let Some(ty) = ty {
                    self.write(&format!(": {}", Self::rust_type(ty)));
                }

                self.write(" = ");
                if let Some(init) = init {
                    self.generate_expr(init);
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
                        self.write_indent();
                        self.generate_expr(target);
                        self.write(" = ");
                        self.generate_expr(target);
                        let method = match op {
                            BinaryOp::Add => ".wrapping_add(",
                            BinaryOp::Sub => ".wrapping_sub(",
                            BinaryOp::Mul => ".wrapping_mul(",
                            _ => unreachable!(),
                        };
                        self.write(method);
                        self.generate_expr(value);
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
                self.write_indent();
                self.write(&format!("for {} in ", var.name));
                self.generate_expr(start);
                if *inclusive {
                    self.write("..=");
                } else {
                    self.write("..");
                }
                self.generate_expr(end);
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
                        let suffix = Self::infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, suffix);
                        self.write(".wrapping_add(");
                        self.generate_typed_expr(right, suffix);
                        self.write(")");
                    }
                    BinaryOp::Sub => {
                        let suffix = Self::infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, suffix);
                        self.write(".wrapping_sub(");
                        self.generate_typed_expr(right, suffix);
                        self.write(")");
                    }
                    BinaryOp::Mul => {
                        let suffix = Self::infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, suffix);
                        self.write(".wrapping_mul(");
                        self.generate_typed_expr(right, suffix);
                        self.write(")");
                    }
                    BinaryOp::Shl => {
                        let suffix = Self::infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, suffix);
                        self.write(".wrapping_shl(");
                        self.generate_expr(right);
                        self.write(" as u32)");
                    }
                    BinaryOp::Shr => {
                        let suffix = Self::infer_wrapping_suffix(left, right);
                        self.generate_typed_expr(left, suffix);
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
            self.write(&format!("{}::{}(", rust_ty, byte_method));
            self.generate_slice_ref(expr);
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
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => Self::rust_native_type(p.to_native()),
            TypeKind::Array { element, size } => {
                format!("[{}; {}]", Self::rust_type(element), size)
            }
            TypeKind::Slice { element } => {
                format!("&[{}]", Self::rust_type(element))
            }
            TypeKind::ArrayRef { element, size } => {
                format!("&[{}; {}]", Self::rust_type(element), size)
            }
            TypeKind::MutRef(inner) => {
                // Handle MutRef(Slice(T)) => &mut [T] (not &mut &[T])
                if let TypeKind::Slice { element } = &inner.kind {
                    format!("&mut [{}]", Self::rust_type(element))
                } else {
                    format!("&mut {}", Self::rust_type(inner))
                }
            }
            TypeKind::Ref(inner) => {
                // Handle Ref(Slice(T)) => &[T] (not &&[T])
                if let TypeKind::Slice { element } = &inner.kind {
                    format!("&[{}]", Self::rust_type(element))
                } else {
                    format!("&{}", Self::rust_type(inner))
                }
            }
            TypeKind::Named(ident) => ident.name.clone(),
            TypeKind::SelfType => "Self".to_string(),
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

    /// Determine the type suffix needed for wrapping operations.
    /// If either operand is an integer literal, we need a suffix to avoid ambiguity.
    /// Returns the suffix to apply to integer literals (empty string if no literals present).
    fn infer_wrapping_suffix(left: &Expr, right: &Expr) -> &'static str {
        let left_is_lit = matches!(left.kind, ExprKind::Integer(_));
        let right_is_lit = matches!(right.kind, ExprKind::Integer(_));

        if !left_is_lit && !right_is_lit {
            // Neither side is a literal, no suffix needed
            return "";
        }

        // Try to infer from the non-literal side
        if left_is_lit && !right_is_lit {
            let s = Self::infer_int_type_suffix(right);
            if !s.is_empty() {
                return s;
            }
        }
        if right_is_lit && !left_is_lit {
            let s = Self::infer_int_type_suffix(left);
            if !s.is_empty() {
                return s;
            }
        }

        // Both are literals or we couldn't infer - default to u64
        // (most common integer type in crypto code)
        "u64"
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

    /// Convert a parser type to a Rust type string, adding lifetime 'a to references
    fn rust_type_with_lifetime(ty: &crate::parser::Type) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Slice { element } => {
                format!("&'a [{}]", Self::rust_type(element))
            }
            TypeKind::Ref(inner) => {
                format!("&'a {}", Self::rust_type(inner))
            }
            TypeKind::MutRef(inner) => {
                format!("&'a mut {}", Self::rust_type(inner))
            }
            TypeKind::ArrayRef { element, size } => {
                format!("&'a [{}; {}]", Self::rust_type(element), size)
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
