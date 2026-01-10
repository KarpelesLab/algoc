//! JavaScript code generator
//!
//! Generates JavaScript code from the analyzed AST.
//! Uses TypedArrays for byte buffers and handles bitwise operations.

use std::collections::{HashSet, HashMap};
use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;
use crate::parser::{
    Ast, Item, ItemKind, Function, Stmt, StmtKind, Expr, ExprKind,
    BinaryOp, UnaryOp, BuiltinFunc, Block, Type as ParserType,
};
use super::CodeGenerator;

/// Struct field info for code generation
#[derive(Clone)]
struct StructFieldInfo {
    name: String,
    ty: ParserType,
}

/// JavaScript code generator
pub struct JavaScriptGenerator {
    /// Current indentation level
    indent: usize,
    /// Output buffer
    output: String,
    /// Whether to include test functions and runner
    include_tests: bool,
    /// Variables that hold BigInt values (u64/i64/u128/i128)
    bigint_vars: HashSet<String>,
    /// Functions that return BigInt values (u64/i64/u128/i128)
    bigint_funcs: HashSet<String>,
    /// Struct fields that are BigInt types (struct_name.field_name)
    bigint_fields: HashSet<String>,
    /// Whether the current function returns a BigInt type
    current_func_returns_bigint: bool,
    /// Struct definitions for read/write generation
    struct_defs: HashMap<String, Vec<StructFieldInfo>>,
    /// Variable types (for struct read/write generation)
    var_types: HashMap<String, String>,
}

impl JavaScriptGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            bigint_vars: HashSet::new(),
            bigint_funcs: HashSet::new(),
            bigint_fields: HashSet::new(),
            current_func_returns_bigint: false,
            struct_defs: HashMap::new(),
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
            self.output.push_str("  ");
        }
    }

    fn indent(&mut self) {
        self.indent += 1;
    }

    fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    /// Check if an expression is likely an array type (used for comparison)
    fn is_array_like_expr(&self, expr: &Expr) -> bool {
        match &expr.kind {
            // These builtin expressions produce arrays
            ExprKind::Hex(_) | ExprKind::Bytes(_) | ExprKind::String(_) => true,
            // Array literals
            ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } => true,
            // Slice expressions produce array views
            ExprKind::Slice { .. } => true,
            // References to arrays are still arrays
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Deref(inner) => {
                self.is_array_like_expr(inner)
            }
            // Parenthesized expressions
            ExprKind::Paren(inner) => self.is_array_like_expr(inner),
            // Builtins - only Assert remains and it doesn't return an array
            ExprKind::Builtin { .. } => false,
            // Index into array returns element, not array
            ExprKind::Index { .. } => false,
            // Field access - we don't have type info, so assume primitive (not array)
            // For array field comparisons, users should use constant_time_eq explicitly
            ExprKind::Field { .. } => false,
            // Identifiers - we don't have type info, but commonly arrays are compared
            // We'll assume identifiers being compared are arrays if the other side is
            ExprKind::Ident(_) => false, // Will be caught if other side is array-like
            // Function calls could return arrays
            ExprKind::Call { .. } => false, // Can't know without type info
            // Other expressions
            _ => false,
        }
    }

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        // Most runtime is now in stdlib/runtime.algoc
        // Only generate minimal helpers needed by the compiler
        self.writeln("// AlgoC Runtime Helpers");
        self.writeln("");

        // Reader class for streaming byte input
        self.writeln("class Reader {");
        self.indent();
        self.writeln("constructor(data) {");
        self.indent();
        self.writeln("this.data = data instanceof Uint8Array ? data : new Uint8Array(data);");
        self.writeln("this.pos = 0;");
        self.writeln("this.view = new DataView(this.data.buffer, this.data.byteOffset, this.data.byteLength);");
        self.dedent();
        self.writeln("}");

        // read_u8
        self.writeln("read_u8() {");
        self.indent();
        self.writeln("if (this.pos >= this.data.length) throw new Error('EOF');");
        self.writeln("return this.data[this.pos++];");
        self.dedent();
        self.writeln("}");

        // read_u16 variants
        self.writeln("read_u16() { return this.read_u16be(); }");
        self.writeln("read_u16be() {");
        self.indent();
        self.writeln("if (this.pos + 2 > this.data.length) throw new Error('EOF');");
        self.writeln("const v = this.view.getUint16(this.pos, false);");
        self.writeln("this.pos += 2;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("read_u16le() {");
        self.indent();
        self.writeln("if (this.pos + 2 > this.data.length) throw new Error('EOF');");
        self.writeln("const v = this.view.getUint16(this.pos, true);");
        self.writeln("this.pos += 2;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");

        // read_u32 variants
        self.writeln("read_u32() { return this.read_u32be(); }");
        self.writeln("read_u32be() {");
        self.indent();
        self.writeln("if (this.pos + 4 > this.data.length) throw new Error('EOF');");
        self.writeln("const v = this.view.getUint32(this.pos, false);");
        self.writeln("this.pos += 4;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("read_u32le() {");
        self.indent();
        self.writeln("if (this.pos + 4 > this.data.length) throw new Error('EOF');");
        self.writeln("const v = this.view.getUint32(this.pos, true);");
        self.writeln("this.pos += 4;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");

        // read_u64 variants
        self.writeln("read_u64() { return this.read_u64be(); }");
        self.writeln("read_u64be() {");
        self.indent();
        self.writeln("if (this.pos + 8 > this.data.length) throw new Error('EOF');");
        self.writeln("const v = this.view.getBigUint64(this.pos, false);");
        self.writeln("this.pos += 8;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("read_u64le() {");
        self.indent();
        self.writeln("if (this.pos + 8 > this.data.length) throw new Error('EOF');");
        self.writeln("const v = this.view.getBigUint64(this.pos, true);");
        self.writeln("this.pos += 8;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");

        // read_bytes - exact count, throws if not enough
        self.writeln("read_bytes(count) {");
        self.indent();
        self.writeln("count = Number(count);");
        self.writeln("if (this.pos + count > this.data.length) throw new Error('EOF');");
        self.writeln("const result = this.data.subarray(this.pos, this.pos + count);");
        self.writeln("this.pos += count;");
        self.writeln("return result;");
        self.dedent();
        self.writeln("}");

        // read_chunk - up to max bytes, empty at EOF
        self.writeln("read_chunk(max_size) {");
        self.indent();
        self.writeln("max_size = Number(max_size);");
        self.writeln("const remaining = this.data.length - this.pos;");
        self.writeln("const count = Math.min(max_size, remaining);");
        self.writeln("const result = this.data.subarray(this.pos, this.pos + count);");
        self.writeln("this.pos += count;");
        self.writeln("return result;");
        self.dedent();
        self.writeln("}");

        // eof check
        self.writeln("eof() { return this.pos >= this.data.length; }");

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer class for streaming byte output
        self.writeln("class Writer {");
        self.indent();
        self.writeln("constructor(data) {");
        self.indent();
        self.writeln("this.data = data instanceof Uint8Array ? data : new Uint8Array(data);");
        self.writeln("this.pos = 0;");
        self.writeln("this.view = new DataView(this.data.buffer, this.data.byteOffset, this.data.byteLength);");
        self.dedent();
        self.writeln("}");

        // write_u8
        self.writeln("write_u8(v) {");
        self.indent();
        self.writeln("if (this.pos >= this.data.length) throw new Error('Buffer overflow');");
        self.writeln("this.data[this.pos++] = v & 0xFF;");
        self.dedent();
        self.writeln("}");

        // write_u16 variants
        self.writeln("write_u16(v) { this.write_u16be(v); }");
        self.writeln("write_u16be(v) {");
        self.indent();
        self.writeln("if (this.pos + 2 > this.data.length) throw new Error('Buffer overflow');");
        self.writeln("this.view.setUint16(this.pos, v, false);");
        self.writeln("this.pos += 2;");
        self.dedent();
        self.writeln("}");
        self.writeln("write_u16le(v) {");
        self.indent();
        self.writeln("if (this.pos + 2 > this.data.length) throw new Error('Buffer overflow');");
        self.writeln("this.view.setUint16(this.pos, v, true);");
        self.writeln("this.pos += 2;");
        self.dedent();
        self.writeln("}");

        // write_u32 variants
        self.writeln("write_u32(v) { this.write_u32be(v); }");
        self.writeln("write_u32be(v) {");
        self.indent();
        self.writeln("if (this.pos + 4 > this.data.length) throw new Error('Buffer overflow');");
        self.writeln("this.view.setUint32(this.pos, v, false);");
        self.writeln("this.pos += 4;");
        self.dedent();
        self.writeln("}");
        self.writeln("write_u32le(v) {");
        self.indent();
        self.writeln("if (this.pos + 4 > this.data.length) throw new Error('Buffer overflow');");
        self.writeln("this.view.setUint32(this.pos, v, true);");
        self.writeln("this.pos += 4;");
        self.dedent();
        self.writeln("}");

        // write_u64 variants
        self.writeln("write_u64(v) { this.write_u64be(v); }");
        self.writeln("write_u64be(v) {");
        self.indent();
        self.writeln("if (this.pos + 8 > this.data.length) throw new Error('Buffer overflow');");
        self.writeln("this.view.setBigUint64(this.pos, BigInt(v), false);");
        self.writeln("this.pos += 8;");
        self.dedent();
        self.writeln("}");
        self.writeln("write_u64le(v) {");
        self.indent();
        self.writeln("if (this.pos + 8 > this.data.length) throw new Error('Buffer overflow');");
        self.writeln("this.view.setBigUint64(this.pos, BigInt(v), true);");
        self.writeln("this.pos += 8;");
        self.dedent();
        self.writeln("}");

        // write_bytes - copy byte slice/array
        self.writeln("write_bytes(data) {");
        self.indent();
        self.writeln("if (this.pos + data.length > this.data.length) throw new Error('Buffer overflow');");
        self.writeln("this.data.set(data, this.pos);");
        self.writeln("this.pos += data.length;");
        self.dedent();
        self.writeln("}");

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Generate test runtime helpers (only when include_tests is true)
    fn generate_test_runtime(&mut self) {
        self.writeln("// Test Helpers");
        self.writeln("");

        // Assert function that throws on failure
        self.writeln("let __test_failures = 0;");
        self.writeln("let __test_name = '';");
        self.writeln("");

        self.writeln("function __assert(condition) {");
        self.indent();
        self.writeln("if (!condition) {");
        self.indent();
        self.writeln("__test_failures++;");
        self.writeln("console.log('  ASSERTION FAILED in ' + __test_name);");
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
        }
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        // Clear BigInt variable tracking for this test
        self.bigint_vars.clear();

        self.writeln(&format!("function test_{}() {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        self.write(&format!("const {} = ", c.name.name));
        self.generate_expr(&c.value);
        self.write(";\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Generate a factory function for the struct
        self.writeln(&format!("function create_{}() {{", s.name.name));
        self.indent();
        self.writeln("return {");
        self.indent();
        for (i, field) in s.fields.iter().enumerate() {
            let comma = if i < s.fields.len() - 1 { "," } else { "" };
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{}: {}{}", field.name.name, init, comma));
        }
        self.dedent();
        self.writeln("};");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs
        self.writeln(&format!("function create_{}() {{", l.name.name));
        self.indent();
        self.writeln("return {");
        self.indent();
        for (i, field) in l.fields.iter().enumerate() {
            let comma = if i < l.fields.len() - 1 { "," } else { "" };
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{}: {}{}", field.name.name, init, comma));
        }
        self.dedent();
        self.writeln("};");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum as an object with variant constructors
        // enum Color { Red, Green, Rgb(u8, u8, u8) }
        // becomes:
        // const Color = {
        //     Red: { tag: "Red" },
        //     Green: { tag: "Green" },
        //     Rgb: (v0, v1, v2) => ({ tag: "Rgb", v0, v1, v2 }),
        // };
        self.writeln(&format!("const {} = {{", e.name.name));
        self.indent();
        for (i, variant) in e.variants.iter().enumerate() {
            let comma = if i < e.variants.len() - 1 { "," } else { "" };
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!("{}: {{ tag: \"{}\" }}{}",
                        variant.name.name, variant.name.name, comma));
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    // Generate a factory function: Rgb: (v0, v1, v2) => ({ tag: "Rgb", v0, v1, v2 })
                    let params: Vec<String> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                    let params_str = params.join(", ");
                    self.writeln(&format!("{}: ({}) => ({{ tag: \"{}\", {} }}){}",
                        variant.name.name, params_str, variant.name.name, params_str, comma));
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    // Generate a factory function with named fields
                    let params: Vec<&str> = fields.iter().map(|f| f.name.name.as_str()).collect();
                    let params_str = params.join(", ");
                    let fields_str: Vec<String> = fields.iter()
                        .map(|f| f.name.name.clone())
                        .collect();
                    let fields_obj = fields_str.join(", ");
                    self.writeln(&format!("{}: ({{ {} }}) => ({{ tag: \"{}\", {} }}){}",
                        variant.name.name, params_str, variant.name.name, fields_obj, comma));
                }
            }
        }
        self.dedent();
        self.writeln("};");
        self.writeln("");
    }

    fn default_value_for_type(&self, ty: &crate::parser::Type) -> String {
        match &ty.kind {
            crate::parser::TypeKind::Primitive(p) => {
                let native = p.to_native();
                if matches!(native,
                    crate::parser::PrimitiveType::U64 | crate::parser::PrimitiveType::I64 |
                    crate::parser::PrimitiveType::U128 | crate::parser::PrimitiveType::I128
                ) {
                    "BigInt(0)".to_string()
                } else {
                    "0".to_string()
                }
            }
            crate::parser::TypeKind::Array { element, size } => {
                match &element.kind {
                    crate::parser::TypeKind::Primitive(p) => {
                        match p {
                            crate::parser::PrimitiveType::U8 => format!("new Uint8Array({})", size),
                            crate::parser::PrimitiveType::U16 => format!("new Uint16Array({})", size),
                            crate::parser::PrimitiveType::U32 => format!("new Uint32Array({})", size),
                            _ => format!("new Array({}).fill(0)", size),
                        }
                    }
                    _ => format!("new Array({}).fill(0)", size),
                }
            }
            crate::parser::TypeKind::Named(ident) => {
                // Struct type - call factory function
                format!("create_{}()", ident.name)
            }
            _ => "null".to_string(),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        // Clear BigInt variable tracking for this function
        self.bigint_vars.clear();

        // Track whether this function returns BigInt
        self.current_func_returns_bigint = self.is_bigint_type(func.return_type.as_ref());

        // Track parameters that are BigInt types
        let mut bigint_params = Vec::new();
        for param in &func.params {
            if self.is_bigint_type(Some(&param.ty)) {
                self.bigint_vars.insert(param.name.name.clone());
                bigint_params.push(param.name.name.clone());
            }
        }

        self.write_indent();
        self.write(&format!("function {}(", func.name.name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&param.name.name);
        }

        self.write(") {\n");
        self.indent();

        // Convert BigInt parameters to ensure they're actually BigInt
        // (callers might pass regular numbers)
        for param_name in &bigint_params {
            self.writeln(&format!("{} = BigInt({});", param_name, param_name));
        }

        self.generate_block(&func.body);

        self.dedent();
        self.writeln("}");

        // Reset the flag
        self.current_func_returns_bigint = false;
        self.writeln("");
    }

    fn generate_block(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.generate_stmt(stmt);
        }
    }

    fn generate_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let { name, ty, init, .. } => {
                // Track if this variable holds a BigInt type
                let type_is_bigint = self.is_bigint_type(ty.as_ref());
                let init_is_bigint = init.as_ref().map(|e| self.expr_uses_bigint(e)).unwrap_or(false);
                let is_bigint_type = type_is_bigint || init_is_bigint;
                if is_bigint_type {
                    self.bigint_vars.insert(name.name.clone());
                }

                // Track struct types for read/write generation
                if let Some(ty) = ty {
                    if let crate::parser::TypeKind::Named(type_ident) = &ty.kind {
                        self.var_types.insert(name.name.clone(), type_ident.name.clone());
                    }
                }

                self.write_indent();
                self.write(&format!("let {} = ", name.name));
                if let Some(init) = init {
                    // If type is BigInt but init isn't, wrap in BigInt()
                    if type_is_bigint && !init_is_bigint {
                        self.write("BigInt(");
                        self.generate_expr(init);
                        self.write(")");
                    } else {
                        self.generate_expr(init);
                    }
                } else if let Some(ty) = ty {
                    // Default value for BigInt types
                    if type_is_bigint {
                        self.write("0n");
                    } else {
                        self.write(&self.default_value_for_type(ty));
                    }
                } else {
                    self.write("undefined");
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
                if let ExprKind::Cast { expr: inner, ty } = &target.kind {
                    if let crate::parser::TypeKind::Primitive(p) = &ty.kind {
                        let endian = p.endianness();
                        if endian != crate::parser::Endianness::Native {
                            if let ExprKind::Slice { array, start, end, .. } = &inner.kind {
                                // Generate: new DataView(slice.buffer, slice.byteOffset).setUint32(0, value, littleEndian)
                                let little_endian = endian == crate::parser::Endianness::Little;
                                let (setter, byte_count) = match p.to_native() {
                                    crate::parser::PrimitiveType::U16 | crate::parser::PrimitiveType::I16 => ("setUint16", 2),
                                    crate::parser::PrimitiveType::U32 | crate::parser::PrimitiveType::I32 => ("setUint32", 4),
                                    crate::parser::PrimitiveType::U64 | crate::parser::PrimitiveType::I64 => ("setBigUint64", 8),
                                    _ => ("setUint32", 4),
                                };
                                self.write_indent();
                                self.write("(() => { const __s = ");
                                self.generate_expr(array);
                                self.write(".subarray(");
                                // Array indices must be Numbers, not BigInt
                                if self.expr_uses_bigint(start) {
                                    self.write("Number(");
                                    self.generate_expr(start);
                                    self.write(")");
                                } else {
                                    self.generate_expr(start);
                                }
                                self.write(", ");
                                if self.expr_uses_bigint(end) {
                                    self.write("Number(");
                                    self.generate_expr(end);
                                    self.write(")");
                                } else {
                                    self.generate_expr(end);
                                }
                                self.write(&format!("); new DataView(__s.buffer, __s.byteOffset, {}).{}(0, ", byte_count, setter));
                                if byte_count == 8 {
                                    self.write("BigInt(");
                                    self.generate_expr(value);
                                    self.write(")");
                                } else {
                                    self.generate_expr(value);
                                }
                                self.write(&format!(", {}); }})()", little_endian));
                                self.write(";\n");
                                return;
                            }
                        }
                    }
                }
                // Check if target is a BigInt field or variable
                let target_is_bigint = match &target.kind {
                    ExprKind::Field { field, .. } => self.bigint_fields.contains(&field.name),
                    ExprKind::Ident(ident) => self.bigint_vars.contains(&ident.name),
                    _ => false,
                };
                let value_is_bigint = self.expr_uses_bigint(value);

                self.write_indent();
                self.generate_expr(target);
                self.write(" = ");
                if target_is_bigint && !value_is_bigint {
                    self.write("BigInt(");
                    self.generate_expr(value);
                    self.write(")");
                } else {
                    self.generate_expr(value);
                }
                self.write(";\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                self.write_indent();
                self.generate_expr(target);
                let op_str = match op {
                    BinaryOp::Add => "+=",
                    BinaryOp::Sub => "-=",
                    BinaryOp::Mul => "*=",
                    BinaryOp::Div => "/=",
                    BinaryOp::Rem => "%=",
                    BinaryOp::BitAnd => "&=",
                    BinaryOp::BitOr => "|=",
                    BinaryOp::BitXor => "^=",
                    BinaryOp::Shl => "<<=",
                    BinaryOp::Shr => ">>>=",
                    _ => "=",
                };
                self.write(&format!(" {} ", op_str));
                self.generate_expr(value);
                self.write(";\n");
            }
            StmtKind::If { condition, then_block, else_block } => {
                self.write_indent();
                self.write("if (");
                self.generate_expr(condition);
                self.write(") {\n");
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
            StmtKind::For { var, start, end, inclusive, body } => {
                // Check if bounds use BigInt - if so, convert to Number for the loop
                let start_is_bigint = self.expr_uses_bigint(start);
                let end_is_bigint = self.expr_uses_bigint(end);

                self.write_indent();
                self.write(&format!("for (let {} = ", var.name));
                if start_is_bigint {
                    self.write("Number(");
                    self.generate_expr(start);
                    self.write(")");
                } else {
                    self.generate_expr(start);
                }
                self.write(&format!("; {} {} ", var.name, if *inclusive { "<=" } else { "<" }));
                if end_is_bigint {
                    self.write("Number(");
                    self.generate_expr(end);
                    self.write(")");
                } else {
                    self.generate_expr(end);
                }
                self.write(&format!("; {}++) {{\n", var.name));
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::While { condition, body } => {
                self.write_indent();
                self.write("while (");
                self.generate_expr(condition);
                self.write(") {\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::Loop { body } => {
                self.writeln("while (true) {");
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
                    // If function returns BigInt and expr isn't BigInt, wrap in BigInt()
                    let expr_is_bigint = self.expr_uses_bigint(expr);
                    if self.current_func_returns_bigint && !expr_is_bigint {
                        self.write("BigInt(");
                        self.generate_expr(expr);
                        self.write(")");
                    } else {
                        self.generate_expr(expr);
                    }
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
                // JavaScript numbers can safely represent integers up to 2^53
                // Use regular numbers for all values in that range
                if *n <= (1u128 << 53) {
                    self.write(&format!("{}", n));
                } else {
                    self.write(&format!("{}n", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // Convert string to Uint8Array
                self.write(&format!("new TextEncoder().encode(\"{}\")", escape_js_string(s)));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("new TextEncoder().encode(\"{}\")", escape_js_string(s)));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to Uint8Array
                self.write(&format!("Uint8Array.from('{}'.match(/.{{2}}/g).map(b => parseInt(b, 16)))", h));
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                // For array comparisons, use constant_time_eq instead of ===
                if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
                    let left_is_array = self.is_array_like_expr(left);
                    let right_is_array = self.is_array_like_expr(right);

                    if left_is_array || right_is_array {
                        if matches!(op, BinaryOp::Ne) {
                            self.write("!");
                        }
                        self.write("constant_time_eq(");
                        self.generate_expr(left);
                        self.write(", ");
                        self.generate_expr(right);
                        self.write(")");
                        return;
                    }
                }

                // Check if either operand involves BigInt (u64/i64/u128/i128 casts)
                let left_uses_bigint = self.expr_uses_bigint(left);
                let right_uses_bigint = self.expr_uses_bigint(right);
                let uses_bigint = left_uses_bigint || right_uses_bigint;

                // For bitwise operations on 32-bit values, we need >>> 0 to ensure unsigned
                // But not for BigInt operations (they don't support >>> with regular numbers)
                let needs_unsigned = !uses_bigint && matches!(op,
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul |
                    BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor |
                    BinaryOp::Shl | BinaryOp::Shr
                );

                if needs_unsigned {
                    self.write("(");
                }
                self.write("(");
                // If one side is BigInt and the other is not, wrap in BigInt()
                // for arithmetic, bitwise, and comparison operations
                // (Note: comparison operators like < > work across BigInt and Number,
                // but === and !== require same types)
                let needs_bigint_wrap = matches!(op,
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem |
                    BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor |
                    BinaryOp::Shl | BinaryOp::Shr |
                    BinaryOp::Eq | BinaryOp::Ne | BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge
                );
                if uses_bigint && !left_uses_bigint && needs_bigint_wrap {
                    self.write("BigInt(");
                    self.generate_expr(left);
                    self.write(")");
                } else {
                    self.generate_expr(left);
                }
                let op_str = match op {
                    BinaryOp::Add => " + ",
                    BinaryOp::Sub => " - ",
                    BinaryOp::Mul => " * ",
                    BinaryOp::Div => " / ",
                    BinaryOp::Rem => " % ",
                    BinaryOp::BitAnd => " & ",
                    BinaryOp::BitOr => " | ",
                    BinaryOp::BitXor => " ^ ",
                    BinaryOp::Shl => " << ",
                    BinaryOp::Shr if uses_bigint => " >> ", // BigInt uses >> for right shift
                    BinaryOp::Shr => " >>> ", // Unsigned right shift for regular numbers
                    BinaryOp::Eq => " === ",
                    BinaryOp::Ne => " !== ",
                    BinaryOp::Lt => " < ",
                    BinaryOp::Le => " <= ",
                    BinaryOp::Gt => " > ",
                    BinaryOp::Ge => " >= ",
                    BinaryOp::And => " && ",
                    BinaryOp::Or => " || ",
                };
                self.write(op_str);
                // If one side is BigInt and the other is not, wrap in BigInt()
                if uses_bigint && !right_uses_bigint && needs_bigint_wrap {
                    self.write("BigInt(");
                    self.generate_expr(right);
                    self.write(")");
                } else {
                    self.generate_expr(right);
                }
                self.write(")");
                if needs_unsigned {
                    self.write(" >>> 0)");
                }
            }
            ExprKind::Unary { op, operand } => {
                let op_str = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                    UnaryOp::BitNot => "~",
                };
                self.write(op_str);
                self.write("(");
                self.generate_expr(operand);
                self.write(")");
                // For bitwise not, ensure unsigned
                if matches!(op, UnaryOp::BitNot) {
                    self.write(" >>> 0");
                }
            }
            ExprKind::Index { array, index } => {
                self.generate_expr(array);
                self.write("[");
                // Array indices must be Numbers, not BigInt
                if self.expr_uses_bigint(index) {
                    self.write("Number(");
                    self.generate_expr(index);
                    self.write(")");
                } else {
                    self.generate_expr(index);
                }
                self.write("]");
            }
            ExprKind::Slice { array, start, end, .. } => {
                self.generate_expr(array);
                self.write(".subarray(");
                // Array indices must be Numbers, not BigInt
                if self.expr_uses_bigint(start) {
                    self.write("Number(");
                    self.generate_expr(start);
                    self.write(")");
                } else {
                    self.generate_expr(start);
                }
                self.write(", ");
                if self.expr_uses_bigint(end) {
                    self.write("Number(");
                    self.generate_expr(end);
                    self.write(")");
                } else {
                    self.generate_expr(end);
                }
                self.write(")");
            }
            ExprKind::Field { object, field } => {
                self.generate_expr(object);
                self.write(&format!(".{}", field.name));
            }
            ExprKind::Call { func, args } => {
                // Check for Reader/Writer constructor calls
                if let ExprKind::Ident(ident) = &func.kind {
                    if ident.name == "Reader" || ident.name == "Writer" {
                        self.write(&format!("new {}(", ident.name));
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

                // Check for method calls like slice.len() or reader.read_u32()
                if let ExprKind::Field { object, field } = &func.kind {
                    if field.name == "len" && args.is_empty() {
                        // Convert .len() to .length
                        self.generate_expr(object);
                        self.write(".length");
                        return;
                    }

                    // Handle reader.read(&mut struct) - expand to field reads
                    if field.name == "read" && args.len() == 1 {
                        if let ExprKind::MutRef(inner) = &args[0].kind {
                            if let ExprKind::Ident(var_ident) = &inner.kind {
                                if let Some(struct_name) = self.var_types.get(&var_ident.name).cloned() {
                                    if let Some(fields) = self.struct_defs.get(&struct_name).cloned() {
                                        self.write("(() => { ");
                                        for field_info in &fields {
                                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty) {
                                                self.write(&format!("{}.{} = ", var_ident.name, field_info.name));
                                                self.generate_expr(object);
                                                self.write(&format!(".{}(); ", read_method));
                                            }
                                        }
                                        self.write("})()");
                                        return;
                                    }
                                }
                            }
                        }
                    }

                    // Handle writer.write(&struct) - expand to field writes
                    if field.name == "write" && args.len() == 1 {
                        // Handle both &struct and &mut struct
                        let inner_expr = match &args[0].kind {
                            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => Some(inner.as_ref()),
                            _ => None,
                        };
                        if let Some(inner) = inner_expr {
                            if let ExprKind::Ident(var_ident) = &inner.kind {
                                if let Some(struct_name) = self.var_types.get(&var_ident.name).cloned() {
                                    if let Some(fields) = self.struct_defs.get(&struct_name).cloned() {
                                        self.write("(() => { ");
                                        for field_info in &fields {
                                            if let Some(write_method) = self.get_write_method_for_type(&field_info.ty) {
                                                self.generate_expr(object);
                                                self.write(&format!(".{}({}.{}); ", write_method, var_ident.name, field_info.name));
                                            }
                                        }
                                        self.write("})()");
                                        return;
                                    }
                                }
                            }
                        }
                    }

                    // Reader/Writer method calls - pass through directly
                    let reader_methods = ["read_u8", "read_u16", "read_u16be", "read_u16le",
                        "read_u32", "read_u32be", "read_u32le", "read_u64", "read_u64be", "read_u64le",
                        "read_bytes", "read_chunk", "eof"];
                    let writer_methods = ["write_u8", "write_u16", "write_u16be", "write_u16le",
                        "write_u32", "write_u32be", "write_u32le", "write_u64", "write_u64be", "write_u64le",
                        "write_bytes"];
                    if reader_methods.contains(&field.name.as_str()) || writer_methods.contains(&field.name.as_str()) {
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
                }

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
                // Generate as typed array if possible
                if elements.is_empty() {
                    self.write("[]");
                } else {
                    // Check if all elements are small integers (bytes)
                    let all_bytes = elements.iter().all(|e| {
                        if let ExprKind::Integer(n) = &e.kind {
                            *n <= 255
                        } else {
                            false
                        }
                    });
                    let all_ints = elements.iter().all(|e| matches!(e.kind, ExprKind::Integer(_)));

                    if all_bytes {
                        // Use Uint8Array for byte arrays
                        self.write("new Uint8Array([");
                    } else if all_ints {
                        self.write("new Uint32Array([");
                    } else {
                        self.write("[");
                    }
                    for (i, elem) in elements.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(elem);
                    }
                    if all_bytes || all_ints {
                        self.write("])");
                    } else {
                        self.write("]");
                    }
                }
            }
            ExprKind::ArrayRepeat { value, count } => {
                // Check if value is a byte type - use Uint8Array
                let is_byte = self.is_byte_value(value);

                // Check if count is a literal (no need for Number() conversion)
                let count_is_literal = matches!(count.kind, ExprKind::Integer(_));

                if is_byte {
                    // Use Uint8Array for byte arrays
                    self.write("new Uint8Array(");
                    if !count_is_literal {
                        self.write("Number(");
                    }
                    self.generate_expr(count);
                    if !count_is_literal {
                        self.write(")");
                    }
                    self.write(").fill(");
                    self.generate_expr(value);
                    self.write(")");
                } else {
                    // Use regular Array for other types
                    self.write("new Array(");
                    if !count_is_literal {
                        self.write("Number(");
                    }
                    self.generate_expr(count);
                    if !count_is_literal {
                        self.write(")");
                    }
                    self.write(").fill(");
                    self.generate_expr(value);
                    self.write(")");
                }
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in JS are just the value (pass by reference for objects)
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are also no-ops in JS
                self.generate_expr(inner);
            }
            ExprKind::Range { .. } => {
                // Ranges shouldn't appear outside of for loops
                self.write("/* range */");
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.generate_expr(inner);
                self.write(")");
            }
            ExprKind::StructLit { name: _, fields } => {
                self.write("{ ");
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("{}: ", field_name.name));
                    // Check if field is BigInt type and value isn't already BigInt
                    let field_is_bigint = self.bigint_fields.contains(&field_name.name);
                    let value_is_bigint = self.expr_uses_bigint(value);
                    if field_is_bigint && !value_is_bigint {
                        self.write("BigInt(");
                        self.generate_expr(value);
                        self.write(")");
                    } else {
                        self.generate_expr(value);
                    }
                }
                self.write(" }");
            }
            ExprKind::Conditional { condition, then_expr, else_expr } => {
                // JavaScript ternary: condition ? then : else
                self.write("(");
                self.generate_expr(condition);
                self.write(" ? ");
                self.generate_expr(then_expr);
                self.write(" : ");
                self.generate_expr(else_expr);
                self.write(")");
            }
            ExprKind::EnumVariant { enum_name, variant_name, args } => {
                // Generate: EnumName.VariantName or EnumName.VariantName(args...)
                if args.is_empty() {
                    self.write(&format!("{}.{}", enum_name.name, variant_name.name));
                } else {
                    self.write(&format!("{}.{}(", enum_name.name, variant_name.name));
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
                // Generate match as an IIFE with if-else chain
                // match x { A => 1, B => 2 } becomes:
                // ((__match) => { if (__match.tag === "A") return 1; ... })(x)
                self.write("((__match) => { ");
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write(" else ");
                    }
                    self.generate_pattern_match(&arm.pattern, "__match");
                    self.write(" { return ");
                    self.generate_expr(&arm.body);
                    self.write("; }");
                }
                self.write(" })(");
                self.generate_expr(expr);
                self.write(")");
            }
        }
    }

    fn generate_pattern_match(&mut self, pattern: &crate::parser::Pattern, scrutinee: &str) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("if (true)");
            }
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("if ({} === ", scrutinee));
                self.generate_expr(lit_expr);
                self.write(")");
            }
            PatternKind::Ident(ident) => {
                // Binding pattern - always matches, bind the value
                self.write(&format!("if ((() => {{ let {} = {}; return true; }})())", ident.name, scrutinee));
            }
            PatternKind::EnumVariant { enum_name: _, variant_name, bindings } => {
                // Check the tag matches
                self.write(&format!("if ({}.tag === \"{}\"", scrutinee, variant_name.name));
                // If there are bindings, we need to extract them
                if !bindings.is_empty() {
                    // For now, just check the tag; bindings are handled in the body
                    // In a more complete impl, we'd extract v0, v1, etc.
                }
                self.write(")");
            }
            PatternKind::Tuple(_patterns) => {
                // Tuple patterns for destructuring
                self.write("if (true)"); // Simplified for now
            }
            PatternKind::Or(patterns) => {
                self.write("if (");
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" || ");
                    }
                    self.write("(");
                    // Inline the condition for each sub-pattern
                    self.generate_pattern_condition(p, scrutinee);
                    self.write(")");
                }
                self.write(")");
            }
        }
    }

    fn generate_pattern_condition(&mut self, pattern: &crate::parser::Pattern, scrutinee: &str) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => self.write("true"),
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("{} === ", scrutinee));
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(_) => self.write("true"),
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!("{}.tag === \"{}\"", scrutinee, variant_name.name));
            }
            PatternKind::Tuple(_) => self.write("true"),
            PatternKind::Or(patterns) => {
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" || ");
                    }
                    self.write("(");
                    self.generate_pattern_condition(p, scrutinee);
                    self.write(")");
                }
            }
        }
    }

    /// Get the Reader method name for reading a field type
    fn get_read_method_for_type(&self, ty: &ParserType) -> Option<String> {
        use crate::parser::{TypeKind, PrimitiveType, Endianness};

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
        use crate::parser::{TypeKind, PrimitiveType, Endianness};

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

    /// Generate code to read a struct from a Reader
    fn generate_struct_read(&mut self, reader_expr: &Expr, struct_expr: &Expr, struct_name: &str) {
        if let Some(fields) = self.struct_defs.get(struct_name).cloned() {
            for field in &fields {
                if let Some(read_method) = self.get_read_method_for_type(&field.ty) {
                    self.write_indent();
                    self.generate_expr(struct_expr);
                    self.write(&format!(".{} = ", field.name));
                    self.generate_expr(reader_expr);
                    self.write(&format!(".{}();\n", read_method));
                }
                // TODO: Handle nested structs, arrays, etc.
            }
        }
    }

    /// Generate code to write a struct to a Writer
    fn generate_struct_write(&mut self, writer_expr: &Expr, struct_expr: &Expr, struct_name: &str) {
        if let Some(fields) = self.struct_defs.get(struct_name).cloned() {
            for field in &fields {
                if let Some(write_method) = self.get_write_method_for_type(&field.ty) {
                    self.write_indent();
                    self.generate_expr(writer_expr);
                    self.write(&format!(".{}(", write_method));
                    self.generate_expr(struct_expr);
                    self.write(&format!(".{});\n", field.name));
                }
                // TODO: Handle nested structs, arrays, etc.
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
        use crate::parser::{TypeKind, PrimitiveType, Endianness};

        // Check for endian byte conversions (byte slice/array to integer)
        // e.g., buf[0..4] as u32be -> use DataView
        if let TypeKind::Primitive(p) = &ty.kind {
            let endian = p.endianness();
            if endian != Endianness::Native {
                // This is an endian-qualified type
                let little_endian = endian == Endianness::Little;
                let native = p.to_native();

                // Check if source is a slice/array (byte conversion)
                if self.is_byte_sequence_expr(expr) {
                    // Use DataView to read the bytes
                    // new DataView(buf.buffer, buf.byteOffset, buf.byteLength).getUint32(0, littleEndian)
                    let getter = match native {
                        PrimitiveType::U16 | PrimitiveType::I16 => "getUint16",
                        PrimitiveType::U32 | PrimitiveType::I32 => "getUint32",
                        PrimitiveType::U64 | PrimitiveType::I64 => "getBigUint64",
                        PrimitiveType::U128 | PrimitiveType::I128 => {
                            // JavaScript doesn't have 128-bit support in DataView
                            // Fall back to manual byte manipulation
                            self.write("(() => { const __b = ");
                            self.generate_expr(expr);
                            if little_endian {
                                self.write("; return BigInt(__b[0]) | (BigInt(__b[1]) << 8n) | (BigInt(__b[2]) << 16n) | (BigInt(__b[3]) << 24n) | (BigInt(__b[4]) << 32n) | (BigInt(__b[5]) << 40n) | (BigInt(__b[6]) << 48n) | (BigInt(__b[7]) << 56n) | (BigInt(__b[8]) << 64n) | (BigInt(__b[9]) << 72n) | (BigInt(__b[10]) << 80n) | (BigInt(__b[11]) << 88n) | (BigInt(__b[12]) << 96n) | (BigInt(__b[13]) << 104n) | (BigInt(__b[14]) << 112n) | (BigInt(__b[15]) << 120n); })()");
                            } else {
                                self.write("; return (BigInt(__b[0]) << 120n) | (BigInt(__b[1]) << 112n) | (BigInt(__b[2]) << 104n) | (BigInt(__b[3]) << 96n) | (BigInt(__b[4]) << 88n) | (BigInt(__b[5]) << 80n) | (BigInt(__b[6]) << 72n) | (BigInt(__b[7]) << 64n) | (BigInt(__b[8]) << 56n) | (BigInt(__b[9]) << 48n) | (BigInt(__b[10]) << 40n) | (BigInt(__b[11]) << 32n) | (BigInt(__b[12]) << 24n) | (BigInt(__b[13]) << 16n) | (BigInt(__b[14]) << 8n) | BigInt(__b[15]); })()");
                            }
                            return;
                        }
                        _ => "getUint32", // Fallback
                    };

                    self.write("(() => { const __b = ");
                    self.generate_expr(expr);
                    self.write(&format!("; return new DataView(__b.buffer, __b.byteOffset, __b.byteLength).{}(0, {}); }})()", getter, little_endian));
                    return;
                }

                // Integer to integer with different endianness - just mask
                let source_is_bigint = self.expr_uses_bigint(expr);
                match native {
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        if source_is_bigint {
                            self.write("Number(BigInt.asUintN(16, ");
                            self.generate_expr(expr);
                            self.write("))");
                        } else {
                            self.write("((");
                            self.generate_expr(expr);
                            self.write(") & 0xFFFF)");
                        }
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        self.write("BigInt.asUintN(64, BigInt(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    _ => {
                        if source_is_bigint {
                            self.write("Number(BigInt.asUintN(32, ");
                            self.generate_expr(expr);
                            self.write("))");
                        } else {
                            self.write("((");
                            self.generate_expr(expr);
                            self.write(") >>> 0)");
                        }
                    }
                }
                return;
            }
        }

        // Check for integer to byte array cast
        // e.g., value as u8[4] -> create Uint8Array and use DataView
        if let TypeKind::Array { element, size } = &ty.kind {
            if let TypeKind::Primitive(PrimitiveType::U8) = &element.kind {
                // Get the endianness from the source expression
                let (little_endian, bits) = self.get_expr_endianness_info(expr);

                if bits <= 64 {
                    let setter = match bits {
                        16 => "setUint16",
                        64 => "setBigUint64",
                        _ => "setUint32",
                    };

                    self.write(&format!("(() => {{ const __a = new Uint8Array({}); new DataView(__a.buffer).{}(0, ", size, setter));
                    if bits == 64 {
                        self.write("BigInt(");
                        self.generate_expr(expr);
                        self.write(")");
                    } else {
                        self.generate_expr(expr);
                    }
                    self.write(&format!(", {}); return __a; }})()", little_endian));
                    return;
                } else {
                    // 128-bit - manual byte manipulation
                    let inner_expr = if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                        inner
                    } else {
                        expr
                    };

                    self.write(&format!("(() => {{ const __v = BigInt("));
                    self.generate_expr(inner_expr);
                    self.write("); const __a = new Uint8Array(16);");
                    if little_endian {
                        for i in 0..16 {
                            self.write(&format!(" __a[{}] = Number((__v >> {}n) & 0xFFn);", i, i * 8));
                        }
                    } else {
                        for i in 0..16 {
                            self.write(&format!(" __a[{}] = Number((__v >> {}n) & 0xFFn);", i, (15 - i) * 8));
                        }
                    }
                    self.write(" return __a; })()");
                    return;
                }
            }
        }

        // Standard casts - mostly no-ops in JavaScript
        // But we should mask to appropriate bit widths
        let source_is_bigint = self.expr_uses_bigint(expr);

        match &ty.kind {
            TypeKind::Primitive(p) => {
                match p {
                    PrimitiveType::U8 | PrimitiveType::I8 => {
                        if source_is_bigint {
                            self.write("Number(BigInt.asUintN(8, ");
                            self.generate_expr(expr);
                            self.write("))");
                        } else {
                            self.write("((");
                            self.generate_expr(expr);
                            self.write(") & 0xFF)");
                        }
                    }
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        if source_is_bigint {
                            self.write("Number(BigInt.asUintN(16, ");
                            self.generate_expr(expr);
                            self.write("))");
                        } else {
                            self.write("((");
                            self.generate_expr(expr);
                            self.write(") & 0xFFFF)");
                        }
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        if source_is_bigint {
                            self.write("Number(BigInt.asUintN(32, ");
                            self.generate_expr(expr);
                            self.write("))");
                        } else {
                            self.write("((");
                            self.generate_expr(expr);
                            self.write(") >>> 0)");
                        }
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        self.write("BigInt.asUintN(64, BigInt(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    PrimitiveType::U128 | PrimitiveType::I128 => {
                        self.write("BigInt.asUintN(128, BigInt(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    PrimitiveType::Bool => {
                        self.write("!!(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    // Native endian types that need masking
                    _ => {
                        self.generate_expr(expr);
                    }
                }
            }
            _ => {
                self.generate_expr(expr);
            }
        }
    }

    /// Check if an expression produces a byte sequence (for from_bytes conversion)
    fn is_byte_sequence_expr(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Slice { .. } => true,
            ExprKind::Hex(_) | ExprKind::Bytes(_) | ExprKind::String(_) => true,
            ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } => true,
            ExprKind::Index { .. } => false, // Single element
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Paren(inner) => {
                self.is_byte_sequence_expr(inner)
            }
            ExprKind::Ident(_) => true, // Assume variables can be byte sequences
            ExprKind::Field { .. } => true,
            _ => false,
        }
    }

    /// Check if an expression is a plain integer literal (not already BigInt)
    fn is_plain_integer_literal(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Integer(n) => *n <= (1u128 << 53), // Small integers are plain
            ExprKind::Paren(inner) => self.is_plain_integer_literal(inner),
            _ => false,
        }
    }

    /// Check if a type annotation indicates a BigInt type (u64/i64/u128/i128)
    fn is_bigint_type(&self, ty: Option<&crate::parser::Type>) -> bool {
        use crate::parser::{TypeKind, PrimitiveType};

        if let Some(ty) = ty {
            if let TypeKind::Primitive(p) = &ty.kind {
                let native = p.to_native();
                return matches!(native,
                    PrimitiveType::U64 | PrimitiveType::I64 |
                    PrimitiveType::U128 | PrimitiveType::I128
                );
            }
        }
        false
    }

    /// Check if an expression involves BigInt (u64/i64/u128/i128 types)
    fn expr_uses_bigint(&self, expr: &Expr) -> bool {
        use crate::parser::{TypeKind, PrimitiveType};

        match &expr.kind {
            // Cast determines the output type - it's BigInt only if target is BigInt
            ExprKind::Cast { ty, expr: _ } => {
                if let TypeKind::Primitive(p) = &ty.kind {
                    let native = p.to_native();
                    matches!(native,
                        PrimitiveType::U64 | PrimitiveType::I64 |
                        PrimitiveType::U128 | PrimitiveType::I128
                    )
                } else {
                    false
                }
            }
            // Binary operations propagate BigInt
            ExprKind::Binary { left, right, .. } => {
                self.expr_uses_bigint(left) || self.expr_uses_bigint(right)
            }
            // Unary operations propagate BigInt
            ExprKind::Unary { operand, .. } => {
                self.expr_uses_bigint(operand)
            }
            // Parentheses propagate BigInt
            ExprKind::Paren(inner) => self.expr_uses_bigint(inner),
            // Conditional expressions - check all branches
            ExprKind::Conditional { condition, then_expr, else_expr } => {
                self.expr_uses_bigint(condition) ||
                self.expr_uses_bigint(then_expr) ||
                self.expr_uses_bigint(else_expr)
            }
            // Large integer literals become BigInt
            ExprKind::Integer(n) => *n > (1u128 << 53),
            // Check tracked variables
            ExprKind::Ident(ident) => self.bigint_vars.contains(&ident.name),
            // Check function calls - if function returns BigInt type
            ExprKind::Call { func, .. } => {
                if let ExprKind::Ident(ident) = &func.kind {
                    self.bigint_funcs.contains(&ident.name)
                } else {
                    false
                }
            }
            // Check field access - if field is BigInt type
            ExprKind::Field { field, .. } => {
                self.bigint_fields.contains(&field.name)
            }
            // Everything else is not BigInt
            _ => false,
        }
    }

    /// Check if an expression produces a byte value (u8)
    fn is_byte_value(&self, expr: &Expr) -> bool {
        use crate::parser::{TypeKind, PrimitiveType};

        match &expr.kind {
            // Small integer literals are bytes
            ExprKind::Integer(n) => *n <= 255,
            // Cast to u8 produces a byte
            ExprKind::Cast { ty, .. } => {
                if let TypeKind::Primitive(p) = &ty.kind {
                    matches!(p.to_native(), PrimitiveType::U8)
                } else {
                    false
                }
            }
            // Parentheses propagate byte type
            ExprKind::Paren(inner) => self.is_byte_value(inner),
            _ => false,
        }
    }

    /// Get endianness info from an expression (little_endian, bits)
    fn get_expr_endianness_info(&self, expr: &Expr) -> (bool, u32) {
        use crate::parser::{TypeKind, PrimitiveType, Endianness};

        if let ExprKind::Cast { ty, .. } = &expr.kind {
            if let TypeKind::Primitive(p) = &ty.kind {
                let endian = p.endianness();
                let little = endian == Endianness::Little;
                let bits = match p.to_native() {
                    PrimitiveType::U16 | PrimitiveType::I16 => 16,
                    PrimitiveType::U32 | PrimitiveType::I32 => 32,
                    PrimitiveType::U64 | PrimitiveType::I64 => 64,
                    PrimitiveType::U128 | PrimitiveType::I128 => 128,
                    _ => 32,
                };
                return (little, bits);
            }
        }
        // Default to little endian, 32 bits
        (true, 32)
    }
}

impl Default for JavaScriptGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for JavaScriptGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.bigint_funcs.clear();
        self.bigint_fields.clear();
        self.struct_defs.clear();

        // Pre-pass: collect functions that return BigInt types and struct fields that are BigInt
        for item in &ast.ast.items {
            match &item.kind {
                ItemKind::Function(func) => {
                    if let Some(ret_ty) = &func.return_type {
                        if self.is_bigint_type(Some(ret_ty)) {
                            self.bigint_funcs.insert(func.name.name.clone());
                        }
                    }
                }
                ItemKind::Struct(s) => {
                    // Collect struct field info for read/write generation
                    let fields: Vec<StructFieldInfo> = s.fields.iter().map(|f| StructFieldInfo {
                        name: f.name.name.clone(),
                        ty: f.ty.clone(),
                    }).collect();
                    self.struct_defs.insert(s.name.name.clone(), fields);

                    for field in &s.fields {
                        if self.is_bigint_type(Some(&field.ty)) {
                            // Use just the field name since we don't track struct types at access points
                            self.bigint_fields.insert(field.name.name.clone());
                        }
                    }
                }
                ItemKind::Layout(l) => {
                    // Also collect layout field info
                    let fields: Vec<StructFieldInfo> = l.fields.iter().map(|f| StructFieldInfo {
                        name: f.name.name.clone(),
                        ty: f.ty.clone(),
                    }).collect();
                    self.struct_defs.insert(l.name.name.clone(), fields);

                    for field in &l.fields {
                        if self.is_bigint_type(Some(&field.ty)) {
                            self.bigint_fields.insert(field.name.name.clone());
                        }
                    }
                }
                _ => {}
            }
        }

        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("");

        self.generate_runtime();

        if self.include_tests {
            self.generate_test_runtime();
        }

        self.generate_ast(&ast.ast);

        // Collect test names for the runner
        let test_names: Vec<_> = ast.ast.items.iter()
            .filter_map(|item| {
                if let ItemKind::Test(t) = &item.kind {
                    Some(t.name.name.clone())
                } else {
                    None
                }
            })
            .collect();

        // Generate test runner if tests are included
        if self.include_tests && !test_names.is_empty() {
            self.writeln("// Test Runner");
            self.writeln("function run_tests() {");
            self.indent();
            self.writeln("let __passed = 0;");
            self.writeln("let __failed = 0;");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("__test_name = '{}';", name));
                self.writeln("__test_failures = 0;");
                self.writeln("try {");
                self.indent();
                self.writeln(&format!("test_{}();", name));
                self.writeln("if (__test_failures === 0) {");
                self.indent();
                self.writeln(&format!("console.log('PASS: {}');", name));
                self.writeln("__passed++;");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("console.log('FAIL: {}');", name));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("} catch (e) {");
                self.indent();
                self.writeln(&format!("console.log('FAIL: {} - ' + e.message);", name));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("console.log('');");
            self.writeln("console.log(__passed + ' passed, ' + __failed + ' failed');");
            self.writeln("return __failed === 0;");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // Export functions and struct creators
        self.writeln("// Exports");
        self.writeln("if (typeof module !== 'undefined' && module.exports) {");
        self.indent();
        self.write_indent();
        self.write("module.exports = { ");
        let mut first = true;
        // Export struct creators
        for item in &ast.ast.items {
            if let ItemKind::Struct(s) = &item.kind {
                if !first {
                    self.write(", ");
                }
                self.write(&format!("create_{}", s.name.name));
                first = false;
            }
        }
        // Export functions
        for item in &ast.ast.items {
            if let ItemKind::Function(func) = &item.kind {
                if !first {
                    self.write(", ");
                }
                self.write(&func.name.name);
                first = false;
            }
        }
        if self.include_tests && !test_names.is_empty() {
            if !first {
                self.write(", ");
            }
            self.write("run_tests");
        }
        self.write(" };\n");
        self.dedent();
        self.writeln("}");

        // Auto-run tests if this is the main module
        if self.include_tests && !test_names.is_empty() {
            self.writeln("");
            self.writeln("// Auto-run tests if executed directly");
            self.writeln("if (typeof require !== 'undefined' && require.main === module) {");
            self.indent();
            self.writeln("process.exit(run_tests() ? 0 : 1);");
            self.dedent();
            self.writeln("}");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "js"
    }

    fn language_name(&self) -> &'static str {
        "JavaScript"
    }
}

fn escape_js_string(s: &str) -> String {
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
