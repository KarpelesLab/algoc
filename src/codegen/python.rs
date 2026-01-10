//! Python code generator
//!
//! Generates Python code from the analyzed AST.
//! Uses bytearray for mutable byte buffers and handles bitwise operations.

use std::collections::HashMap;
use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;
use crate::parser::{
    Ast, Item, ItemKind, Function, Stmt, StmtKind, Expr, ExprKind,
    BinaryOp, UnaryOp, BuiltinFunc, Block, Type as ParserType,
};
use super::CodeGenerator;

/// Struct field info for read/write generation
#[derive(Clone)]
struct StructFieldInfo {
    name: String,
    ty: ParserType,
}

/// Python code generator
pub struct PythonGenerator {
    /// Current indentation level
    indent: usize,
    /// Output buffer
    output: String,
    /// Whether to include test functions and runner
    include_tests: bool,
    /// Struct definitions for read/write generation
    struct_defs: HashMap<String, Vec<StructFieldInfo>>,
    /// Variable types (for struct read/write generation)
    var_types: HashMap<String, String>,
}

impl PythonGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
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
            self.output.push_str("    ");
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
            ExprKind::Hex(_) | ExprKind::Bytes(_) | ExprKind::String(_) => true,
            ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } => true,
            ExprKind::Slice { .. } => true,
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Deref(inner) => {
                self.is_array_like_expr(inner)
            }
            ExprKind::Paren(inner) => self.is_array_like_expr(inner),
            ExprKind::Builtin { .. } => false,
            ExprKind::Index { .. } => false,
            // Field access - we don't have type info, so assume primitive (not array)
            // For array field comparisons, users should use constant_time_eq explicitly
            ExprKind::Field { .. } => false,
            ExprKind::Ident(_) => false,
            ExprKind::Call { .. } => false,
            _ => false,
        }
    }

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        self.writeln("# AlgoC Runtime Helpers");
        self.writeln("");

        // Helper for masking to specific bit widths
        self.writeln("def _u32(x):");
        self.indent();
        self.writeln("return x & 0xFFFFFFFF");
        self.dedent();
        self.writeln("");

        self.writeln("def _u64(x):");
        self.indent();
        self.writeln("return x & 0xFFFFFFFFFFFFFFFF");
        self.dedent();
        self.writeln("");

        self.writeln("def _u8(x):");
        self.indent();
        self.writeln("return x & 0xFF");
        self.dedent();
        self.writeln("");

        // Reader class for streaming byte input
        self.writeln("class Reader:");
        self.indent();
        self.writeln("def __init__(self, data):");
        self.indent();
        self.writeln("self.data = bytes(data) if not isinstance(data, (bytes, bytearray)) else data");
        self.writeln("self.pos = 0");
        self.dedent();
        self.writeln("");

        // read_u8
        self.writeln("def read_u8(self):");
        self.indent();
        self.writeln("if self.pos >= len(self.data): raise EOFError('EOF')");
        self.writeln("v = self.data[self.pos]");
        self.writeln("self.pos += 1");
        self.writeln("return v");
        self.dedent();
        self.writeln("");

        // read_u16 variants
        self.writeln("def read_u16(self): return self.read_u16be()");
        self.writeln("def read_u16be(self):");
        self.indent();
        self.writeln("if self.pos + 2 > len(self.data): raise EOFError('EOF')");
        self.writeln("v = int.from_bytes(self.data[self.pos:self.pos+2], 'big')");
        self.writeln("self.pos += 2");
        self.writeln("return v");
        self.dedent();
        self.writeln("def read_u16le(self):");
        self.indent();
        self.writeln("if self.pos + 2 > len(self.data): raise EOFError('EOF')");
        self.writeln("v = int.from_bytes(self.data[self.pos:self.pos+2], 'little')");
        self.writeln("self.pos += 2");
        self.writeln("return v");
        self.dedent();
        self.writeln("");

        // read_u32 variants
        self.writeln("def read_u32(self): return self.read_u32be()");
        self.writeln("def read_u32be(self):");
        self.indent();
        self.writeln("if self.pos + 4 > len(self.data): raise EOFError('EOF')");
        self.writeln("v = int.from_bytes(self.data[self.pos:self.pos+4], 'big')");
        self.writeln("self.pos += 4");
        self.writeln("return v");
        self.dedent();
        self.writeln("def read_u32le(self):");
        self.indent();
        self.writeln("if self.pos + 4 > len(self.data): raise EOFError('EOF')");
        self.writeln("v = int.from_bytes(self.data[self.pos:self.pos+4], 'little')");
        self.writeln("self.pos += 4");
        self.writeln("return v");
        self.dedent();
        self.writeln("");

        // read_u64 variants
        self.writeln("def read_u64(self): return self.read_u64be()");
        self.writeln("def read_u64be(self):");
        self.indent();
        self.writeln("if self.pos + 8 > len(self.data): raise EOFError('EOF')");
        self.writeln("v = int.from_bytes(self.data[self.pos:self.pos+8], 'big')");
        self.writeln("self.pos += 8");
        self.writeln("return v");
        self.dedent();
        self.writeln("def read_u64le(self):");
        self.indent();
        self.writeln("if self.pos + 8 > len(self.data): raise EOFError('EOF')");
        self.writeln("v = int.from_bytes(self.data[self.pos:self.pos+8], 'little')");
        self.writeln("self.pos += 8");
        self.writeln("return v");
        self.dedent();
        self.writeln("");

        // read_bytes - exact count, throws if not enough
        self.writeln("def read_bytes(self, count):");
        self.indent();
        self.writeln("count = int(count)");
        self.writeln("if self.pos + count > len(self.data): raise EOFError('EOF')");
        self.writeln("result = self.data[self.pos:self.pos+count]");
        self.writeln("self.pos += count");
        self.writeln("return result");
        self.dedent();
        self.writeln("");

        // read_chunk - up to max bytes, empty at EOF
        self.writeln("def read_chunk(self, max_size):");
        self.indent();
        self.writeln("max_size = int(max_size)");
        self.writeln("remaining = len(self.data) - self.pos");
        self.writeln("count = min(max_size, remaining)");
        self.writeln("result = self.data[self.pos:self.pos+count]");
        self.writeln("self.pos += count");
        self.writeln("return result");
        self.dedent();
        self.writeln("");

        // eof check
        self.writeln("def eof(self): return self.pos >= len(self.data)");

        self.dedent();
        self.writeln("");

        // Writer class for streaming byte output
        // Uses byte-by-byte writes to work with both lists and bytearrays
        self.writeln("class Writer:");
        self.indent();
        self.writeln("def __init__(self, data):");
        self.indent();
        self.writeln("self.data = data");
        self.writeln("self.pos = 0");
        self.dedent();
        self.writeln("");

        // write_u8
        self.writeln("def write_u8(self, v):");
        self.indent();
        self.writeln("if self.pos >= len(self.data): raise BufferError('Buffer overflow')");
        self.writeln("self.data[self.pos] = v & 0xFF");
        self.writeln("self.pos += 1");
        self.dedent();
        self.writeln("");

        // write_u16 variants - byte-by-byte for list compatibility
        self.writeln("def write_u16(self, v): self.write_u16be(v)");
        self.writeln("def write_u16be(self, v):");
        self.indent();
        self.writeln("if self.pos + 2 > len(self.data): raise BufferError('Buffer overflow')");
        self.writeln("self.data[self.pos] = (v >> 8) & 0xFF");
        self.writeln("self.data[self.pos + 1] = v & 0xFF");
        self.writeln("self.pos += 2");
        self.dedent();
        self.writeln("def write_u16le(self, v):");
        self.indent();
        self.writeln("if self.pos + 2 > len(self.data): raise BufferError('Buffer overflow')");
        self.writeln("self.data[self.pos] = v & 0xFF");
        self.writeln("self.data[self.pos + 1] = (v >> 8) & 0xFF");
        self.writeln("self.pos += 2");
        self.dedent();
        self.writeln("");

        // write_u32 variants - byte-by-byte for list compatibility
        self.writeln("def write_u32(self, v): self.write_u32be(v)");
        self.writeln("def write_u32be(self, v):");
        self.indent();
        self.writeln("if self.pos + 4 > len(self.data): raise BufferError('Buffer overflow')");
        self.writeln("self.data[self.pos] = (v >> 24) & 0xFF");
        self.writeln("self.data[self.pos + 1] = (v >> 16) & 0xFF");
        self.writeln("self.data[self.pos + 2] = (v >> 8) & 0xFF");
        self.writeln("self.data[self.pos + 3] = v & 0xFF");
        self.writeln("self.pos += 4");
        self.dedent();
        self.writeln("def write_u32le(self, v):");
        self.indent();
        self.writeln("if self.pos + 4 > len(self.data): raise BufferError('Buffer overflow')");
        self.writeln("self.data[self.pos] = v & 0xFF");
        self.writeln("self.data[self.pos + 1] = (v >> 8) & 0xFF");
        self.writeln("self.data[self.pos + 2] = (v >> 16) & 0xFF");
        self.writeln("self.data[self.pos + 3] = (v >> 24) & 0xFF");
        self.writeln("self.pos += 4");
        self.dedent();
        self.writeln("");

        // write_u64 variants - byte-by-byte for list compatibility
        self.writeln("def write_u64(self, v): self.write_u64be(v)");
        self.writeln("def write_u64be(self, v):");
        self.indent();
        self.writeln("if self.pos + 8 > len(self.data): raise BufferError('Buffer overflow')");
        self.writeln("for i in range(8): self.data[self.pos + i] = (v >> (56 - i * 8)) & 0xFF");
        self.writeln("self.pos += 8");
        self.dedent();
        self.writeln("def write_u64le(self, v):");
        self.indent();
        self.writeln("if self.pos + 8 > len(self.data): raise BufferError('Buffer overflow')");
        self.writeln("for i in range(8): self.data[self.pos + i] = (v >> (i * 8)) & 0xFF");
        self.writeln("self.pos += 8");
        self.dedent();
        self.writeln("");

        // write_bytes - copy byte slice/array byte-by-byte for list compatibility
        self.writeln("def write_bytes(self, data):");
        self.indent();
        self.writeln("if self.pos + len(data) > len(self.data): raise BufferError('Buffer overflow')");
        self.writeln("for i, b in enumerate(data): self.data[self.pos + i] = b");
        self.writeln("self.pos += len(data)");
        self.dedent();

        self.dedent();
        self.writeln("");
    }

    /// Generate test runtime helpers
    fn generate_test_runtime(&mut self) {
        self.writeln("# Test Helpers");
        self.writeln("");
        self.writeln("_test_failures = 0");
        self.writeln("_test_name = ''");
        self.writeln("");

        self.writeln("def _assert(condition):");
        self.indent();
        self.writeln("global _test_failures");
        self.writeln("if not condition:");
        self.indent();
        self.writeln("_test_failures += 1");
        self.writeln("print(f'  ASSERTION FAILED in {_test_name}')");
        self.dedent();
        self.dedent();
        self.writeln("");

        // Helper for constant-time comparison
        self.writeln("def constant_time_eq(a, b):");
        self.indent();
        self.writeln("if len(a) != len(b):");
        self.indent();
        self.writeln("return False");
        self.dedent();
        self.writeln("result = 0");
        self.writeln("for i in range(len(a)):");
        self.indent();
        self.writeln("result |= a[i] ^ b[i]");
        self.dedent();
        self.writeln("return result == 0");
        self.dedent();
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
            ItemKind::Test(test) => {
                if self.include_tests {
                    self.generate_test(test);
                }
            }
            ItemKind::Enum(e) => self.generate_enum(e),
            ItemKind::Use(_) => {
                // Use statements are handled during loading
            }
        }
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("def test_{}():", test.name.name));
        self.indent();
        if test.body.stmts.is_empty() {
            self.writeln("pass");
        } else {
            self.generate_block(&test.body);
        }
        self.dedent();
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        self.write(&format!("{} = ", c.name.name));
        self.generate_expr(&c.value);
        self.write("\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Generate a class for the struct
        self.writeln(&format!("class {}:", s.name.name));
        self.indent();
        self.writeln("def __init__(self):");
        self.indent();
        if s.fields.is_empty() {
            self.writeln("pass");
        } else {
            for field in &s.fields {
                let init = self.default_value_for_type(&field.ty);
                self.writeln(&format!("self.{} = {}", field.name.name, init));
            }
        }
        self.dedent();
        self.dedent();
        self.writeln("");

        // Factory function for consistency
        self.writeln(&format!("def create_{}():", s.name.name));
        self.indent();
        self.writeln(&format!("return {}()", s.name.name));
        self.dedent();
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs
        self.writeln(&format!("class {}:", l.name.name));
        self.indent();
        self.writeln("def __init__(self):");
        self.indent();
        if l.fields.is_empty() {
            self.writeln("pass");
        } else {
            for field in &l.fields {
                let init = self.default_value_for_type(&field.ty);
                self.writeln(&format!("self.{} = {}", field.name.name, init));
            }
        }
        self.dedent();
        self.dedent();
        self.writeln("");

        self.writeln(&format!("def create_{}():", l.name.name));
        self.indent();
        self.writeln(&format!("return {}()", l.name.name));
        self.dedent();
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum as a class with variant constructors
        // enum Color { Red, Green, Rgb(u8, u8, u8) }
        // becomes:
        // class Color:
        //     class Red:
        //         tag = "Red"
        //     class Rgb:
        //         def __init__(self, v0, v1, v2):
        //             self.tag = "Rgb"
        //             self.v0 = v0
        //             ...
        self.writeln(&format!("class {}:", e.name.name));
        self.indent();

        if e.variants.is_empty() {
            self.writeln("pass");
        } else {
            for variant in &e.variants {
                match &variant.data {
                    crate::parser::EnumVariantData::Unit => {
                        // Unit variant becomes a singleton instance
                        self.writeln(&format!("class _{}:", variant.name.name));
                        self.indent();
                        self.writeln(&format!("tag = \"{}\"", variant.name.name));
                        self.dedent();
                        self.writeln(&format!("{} = _{}()", variant.name.name, variant.name.name));
                    }
                    crate::parser::EnumVariantData::Tuple(types) => {
                        // Tuple variant becomes a class with positional args
                        self.writeln(&format!("class {}:", variant.name.name));
                        self.indent();
                        let params: Vec<String> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                        let params_str = params.join(", ");
                        self.writeln(&format!("def __init__(self, {}):", params_str));
                        self.indent();
                        self.writeln(&format!("self.tag = \"{}\"", variant.name.name));
                        for (i, _) in types.iter().enumerate() {
                            self.writeln(&format!("self.v{} = v{}", i, i));
                        }
                        self.dedent();
                        self.dedent();
                    }
                    crate::parser::EnumVariantData::Struct(fields) => {
                        // Struct variant becomes a class with named args
                        self.writeln(&format!("class {}:", variant.name.name));
                        self.indent();
                        let params: Vec<&str> = fields.iter().map(|f| f.name.name.as_str()).collect();
                        let params_str = params.join(", ");
                        self.writeln(&format!("def __init__(self, {}):", params_str));
                        self.indent();
                        self.writeln(&format!("self.tag = \"{}\"", variant.name.name));
                        for field in fields {
                            self.writeln(&format!("self.{} = {}", field.name.name, field.name.name));
                        }
                        self.dedent();
                        self.dedent();
                    }
                }
            }
        }
        self.dedent();
        self.writeln("");
    }

    fn default_value_for_type(&self, ty: &crate::parser::Type) -> String {
        match &ty.kind {
            crate::parser::TypeKind::Primitive(_) => "0".to_string(),
            crate::parser::TypeKind::Array { element, size } => {
                match &element.kind {
                    crate::parser::TypeKind::Primitive(p) => {
                        match p {
                            crate::parser::PrimitiveType::U8 => format!("bytearray({})", size),
                            _ => format!("[0] * {}", size),
                        }
                    }
                    _ => format!("[0] * {}", size),
                }
            }
            crate::parser::TypeKind::Named(ident) => {
                format!("create_{}()", ident.name)
            }
            _ => "None".to_string(),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        self.write_indent();
        self.write(&format!("def {}(", func.name.name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&param.name.name);
        }

        self.write("):\n");
        self.indent();

        if func.body.stmts.is_empty() {
            self.writeln("pass");
        } else {
            self.generate_block(&func.body);
        }

        self.dedent();
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
                // Track variable type for struct read/write generation
                if let Some(ty) = ty {
                    if let crate::parser::TypeKind::Named(type_ident) = &ty.kind {
                        self.var_types.insert(name.name.clone(), type_ident.name.clone());
                    }
                }

                self.write_indent();
                self.write(&format!("{} = ", name.name));
                if let Some(init) = init {
                    // Check if init is a struct literal - need special handling
                    if let ExprKind::StructLit { name: struct_name, fields } = &init.kind {
                        // Create the struct
                        self.write(&format!("{}()\n", struct_name.name));
                        // Assign each field
                        for (field_name, field_value) in fields {
                            self.write_indent();
                            self.write(&format!("{}.{} = ", name.name, field_name.name));
                            self.generate_expr(field_value);
                            self.write("\n");
                        }
                    } else {
                        self.generate_expr(init);
                        self.write("\n");
                    }
                } else if let Some(ty) = ty {
                    self.write(&self.default_value_for_type(ty));
                    self.write("\n");
                } else {
                    self.write("None\n");
                }
            }
            StmtKind::Expr(expr) => {
                self.write_indent();
                self.generate_expr(expr);
                self.write("\n");
            }
            StmtKind::Assign { target, value } => {
                // Check for endian cast assignment: buf[0..4] as u32be = value
                if let ExprKind::Cast { expr: inner, ty } = &target.kind {
                    if let crate::parser::TypeKind::Primitive(p) = &ty.kind {
                        let endian = p.endianness();
                        if endian != crate::parser::Endianness::Native {
                            if let ExprKind::Slice { array, start, end, .. } = &inner.kind {
                                // Generate: array[start:end] = value.to_bytes(N, 'big'/'little')
                                let byte_order = if endian == crate::parser::Endianness::Big {
                                    "'big'"
                                } else {
                                    "'little'"
                                };
                                let byte_count = match p.to_native() {
                                    crate::parser::PrimitiveType::U16 | crate::parser::PrimitiveType::I16 => 2,
                                    crate::parser::PrimitiveType::U32 | crate::parser::PrimitiveType::I32 => 4,
                                    crate::parser::PrimitiveType::U64 | crate::parser::PrimitiveType::I64 => 8,
                                    crate::parser::PrimitiveType::U128 | crate::parser::PrimitiveType::I128 => 16,
                                    _ => 4,
                                };
                                self.write_indent();
                                self.generate_expr(array);
                                self.write("[");
                                self.generate_expr(start);
                                self.write(":");
                                self.generate_expr(end);
                                self.write("] = list((");
                                self.generate_expr(value);
                                self.write(&format!(").to_bytes({}, {}))\n", byte_count, byte_order));
                                return;
                            }
                        }
                    }
                }
                self.write_indent();
                self.generate_expr(target);
                self.write(" = ");
                self.generate_expr(value);
                self.write("\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                self.write_indent();
                self.generate_expr(target);
                let op_str = match op {
                    BinaryOp::Add => " += ",
                    BinaryOp::Sub => " -= ",
                    BinaryOp::Mul => " *= ",
                    BinaryOp::Div => " //= ",
                    BinaryOp::Rem => " %= ",
                    BinaryOp::BitAnd => " &= ",
                    BinaryOp::BitOr => " |= ",
                    BinaryOp::BitXor => " ^= ",
                    BinaryOp::Shl => " <<= ",
                    BinaryOp::Shr => " >>= ",
                    _ => " = ",
                };
                self.write(op_str);
                self.generate_expr(value);
                self.write("\n");
            }
            StmtKind::If { condition, then_block, else_block } => {
                self.write_indent();
                self.write("if ");
                self.generate_expr(condition);
                self.write(":\n");
                self.indent();
                if then_block.stmts.is_empty() {
                    self.writeln("pass");
                } else {
                    self.generate_block(then_block);
                }
                self.dedent();
                if let Some(else_block) = else_block {
                    self.writeln("else:");
                    self.indent();
                    if else_block.stmts.is_empty() {
                        self.writeln("pass");
                    } else {
                        self.generate_block(else_block);
                    }
                    self.dedent();
                }
            }
            StmtKind::For { var, start, end, inclusive, body } => {
                self.write_indent();
                self.write(&format!("for {} in range(", var.name));
                self.generate_expr(start);
                self.write(", ");
                if *inclusive {
                    self.generate_expr(end);
                    self.write(" + 1");
                } else {
                    self.generate_expr(end);
                }
                self.write("):\n");
                self.indent();
                if body.stmts.is_empty() {
                    self.writeln("pass");
                } else {
                    self.generate_block(body);
                }
                self.dedent();
            }
            StmtKind::While { condition, body } => {
                self.write_indent();
                self.write("while ");
                self.generate_expr(condition);
                self.write(":\n");
                self.indent();
                if body.stmts.is_empty() {
                    self.writeln("pass");
                } else {
                    self.generate_block(body);
                }
                self.dedent();
            }
            StmtKind::Loop { body } => {
                self.writeln("while True:");
                self.indent();
                if body.stmts.is_empty() {
                    self.writeln("pass");
                } else {
                    self.generate_block(body);
                }
                self.dedent();
            }
            StmtKind::Break => {
                self.writeln("break");
            }
            StmtKind::Continue => {
                self.writeln("continue");
            }
            StmtKind::Return(expr) => {
                self.write_indent();
                if let Some(expr) = expr {
                    self.write("return ");
                    self.generate_expr(expr);
                    self.write("\n");
                } else {
                    self.write("return\n");
                }
            }
            StmtKind::Block(block) => {
                // Python doesn't have block scopes like JS, just inline the statements
                self.generate_block(block);
            }
        }
    }

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                self.write(&format!("{}", n));
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "True" } else { "False" });
            }
            ExprKind::String(s) => {
                // Convert string to bytearray
                self.write(&format!("bytearray(b\"{}\")", escape_py_string(s)));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("bytearray(b\"{}\")", escape_py_string(s)));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to bytearray
                self.write(&format!("bytearray.fromhex('{}')", h));
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                // For array comparisons, use constant_time_eq
                if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
                    let left_is_array = self.is_array_like_expr(left);
                    let right_is_array = self.is_array_like_expr(right);

                    if left_is_array || right_is_array {
                        if matches!(op, BinaryOp::Ne) {
                            self.write("not ");
                        }
                        self.write("constant_time_eq(");
                        self.generate_expr(left);
                        self.write(", ");
                        self.generate_expr(right);
                        self.write(")");
                        return;
                    }
                }

                // Python integers are arbitrary precision, so we need to mask for bitwise ops
                let needs_mask = matches!(op,
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul |
                    BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor |
                    BinaryOp::Shl | BinaryOp::Shr
                );

                if needs_mask {
                    self.write("_u32(");
                }
                self.write("(");
                self.generate_expr(left);
                let op_str = match op {
                    BinaryOp::Add => " + ",
                    BinaryOp::Sub => " - ",
                    BinaryOp::Mul => " * ",
                    BinaryOp::Div => " // ",  // Integer division
                    BinaryOp::Rem => " % ",
                    BinaryOp::BitAnd => " & ",
                    BinaryOp::BitOr => " | ",
                    BinaryOp::BitXor => " ^ ",
                    BinaryOp::Shl => " << ",
                    BinaryOp::Shr => " >> ",
                    BinaryOp::Eq => " == ",
                    BinaryOp::Ne => " != ",
                    BinaryOp::Lt => " < ",
                    BinaryOp::Le => " <= ",
                    BinaryOp::Gt => " > ",
                    BinaryOp::Ge => " >= ",
                    BinaryOp::And => " and ",
                    BinaryOp::Or => " or ",
                };
                self.write(op_str);
                self.generate_expr(right);
                self.write(")");
                if needs_mask {
                    self.write(")");
                }
            }
            ExprKind::Unary { op, operand } => {
                match op {
                    UnaryOp::Neg => {
                        self.write("-");
                        self.write("(");
                        self.generate_expr(operand);
                        self.write(")");
                    }
                    UnaryOp::Not => {
                        self.write("not (");
                        self.generate_expr(operand);
                        self.write(")");
                    }
                    UnaryOp::BitNot => {
                        // Python's ~ on unbounded integers needs masking
                        self.write("_u32(~(");
                        self.generate_expr(operand);
                        self.write("))");
                    }
                }
            }
            ExprKind::Index { array, index } => {
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(index);
                self.write("]");
            }
            ExprKind::Slice { array, start, end, .. } => {
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(start);
                self.write(":");
                self.generate_expr(end);
                self.write("]");
            }
            ExprKind::Field { object, field } => {
                self.generate_expr(object);
                self.write(&format!(".{}", field.name));
            }
            ExprKind::Call { func, args } => {
                // Check for Reader/Writer constructor calls
                if let ExprKind::Ident(ident) = &func.kind {
                    if ident.name == "Reader" || ident.name == "Writer" {
                        self.write(&format!("{}(", ident.name));
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
                        // Convert .len() to len()
                        self.write("len(");
                        self.generate_expr(object);
                        self.write(")");
                        return;
                    }

                    // Handle reader.read(&mut struct) - expand to field reads
                    if field.name == "read" && args.len() == 1 {
                        if let ExprKind::MutRef(inner) = &args[0].kind {
                            if let ExprKind::Ident(var_ident) = &inner.kind {
                                if let Some(struct_name) = self.var_types.get(&var_ident.name).cloned() {
                                    if let Some(fields) = self.struct_defs.get(&struct_name).cloned() {
                                        // Generate: [setattr(obj, 'f1', reader.m1()), setattr(obj, 'f2', reader.m2()), ...]
                                        self.write("[");
                                        let mut first = true;
                                        for field_info in &fields {
                                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty) {
                                                if !first {
                                                    self.write(", ");
                                                }
                                                first = false;
                                                self.write(&format!("setattr({}, '{}', ", var_ident.name, field_info.name));
                                                self.generate_expr(object);
                                                self.write(&format!(".{}())", read_method));
                                            }
                                        }
                                        self.write("]");
                                        return;
                                    }
                                }
                            }
                        }
                    }

                    // Handle writer.write(&struct) - expand to field writes
                    if field.name == "write" && args.len() == 1 {
                        let inner_expr = match &args[0].kind {
                            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => Some(inner.as_ref()),
                            _ => None,
                        };
                        if let Some(inner) = inner_expr {
                            if let ExprKind::Ident(var_ident) = &inner.kind {
                                if let Some(struct_name) = self.var_types.get(&var_ident.name).cloned() {
                                    if let Some(fields) = self.struct_defs.get(&struct_name).cloned() {
                                        // Generate: [writer.m1(obj.f1), writer.m2(obj.f2), ...]
                                        self.write("[");
                                        let mut first = true;
                                        for field_info in &fields {
                                            if let Some(write_method) = self.get_write_method_for_type(&field_info.ty) {
                                                if !first {
                                                    self.write(", ");
                                                }
                                                first = false;
                                                self.generate_expr(object);
                                                self.write(&format!(".{}({}.{})", write_method, var_ident.name, field_info.name));
                                            }
                                        }
                                        self.write("]");
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
                if elements.is_empty() {
                    self.write("[]");
                } else {
                    self.write("[");
                    for (i, elem) in elements.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(elem);
                    }
                    self.write("]");
                }
            }
            ExprKind::ArrayRepeat { value, count } => {
                // Generate [value] * count
                // For mutable arrays, we need to use list comprehension to avoid aliasing
                self.write("[");
                self.generate_expr(value);
                self.write(" for _ in range(");
                self.generate_expr(count);
                self.write(")]");
            }
            ExprKind::Cast { expr, ty } => {
                self.generate_cast(expr, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in Python are just the value
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                self.generate_expr(inner);
            }
            ExprKind::Range { .. } => {
                self.write("# range");
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.generate_expr(inner);
                self.write(")");
            }
            ExprKind::StructLit { name, fields } => {
                // Create struct instance and set fields
                self.write(&format!("{}()", name.name));
                // Note: This doesn't handle field initialization inline
                // For proper struct literals, we'd need a different approach
            }
            ExprKind::Conditional { condition, then_expr, else_expr } => {
                // Python conditional: then_expr if condition else else_expr
                self.write("(");
                self.generate_expr(then_expr);
                self.write(" if ");
                self.generate_expr(condition);
                self.write(" else ");
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
                // Python doesn't have match expressions (until 3.10), so use nested conditionals
                // match x { A => 1, B => 2, _ => 3 } becomes:
                // (1 if x.tag == "A" else (2 if x.tag == "B" else 3))
                // For now, generate a helper lambda
                self.write("(lambda __match: ");
                self.generate_match_arms(arms, 0);
                self.write(")(");
                self.generate_expr(expr);
                self.write(")");
            }
        }
    }

    fn generate_match_arms(&mut self, arms: &[crate::parser::MatchArm], index: usize) {
        if index >= arms.len() {
            self.write("None");  // No arm matched, shouldn't happen with exhaustive matching
            return;
        }

        let arm = &arms[index];
        self.write("(");
        self.generate_expr(&arm.body);
        self.write(" if ");
        self.generate_pattern_condition(&arm.pattern, "__match");
        self.write(" else ");
        self.generate_match_arms(arms, index + 1);
        self.write(")");
    }

    fn generate_pattern_condition(&mut self, pattern: &crate::parser::Pattern, scrutinee: &str) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => self.write("True"),
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("{} == ", scrutinee));
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(_) => self.write("True"),
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!("{}.tag == \"{}\"", scrutinee, variant_name.name));
            }
            PatternKind::Tuple(_) => self.write("True"),
            PatternKind::Or(patterns) => {
                self.write("(");
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" or ");
                    }
                    self.generate_pattern_condition(p, scrutinee);
                }
                self.write(")");
            }
        }
    }

    fn generate_builtin(&mut self, name: BuiltinFunc, args: &[Expr]) {
        match name {
            BuiltinFunc::Assert => {
                self.write("_assert(");
                self.generate_expr(&args[0]);
                self.write(")");
            }
        }
    }

    fn generate_cast(&mut self, expr: &Expr, ty: &crate::parser::Type) {
        use crate::parser::{TypeKind, PrimitiveType, Endianness};

        // Check for endian byte conversions (byte slice/array to integer)
        // e.g., buf[0..4] as u32be -> int.from_bytes(buf[0:4], 'big')
        if let TypeKind::Primitive(p) = &ty.kind {
            let endian = p.endianness();
            if endian != Endianness::Native {
                // This is an endian-qualified type
                let byte_order = if endian == Endianness::Big {
                    "'big'"
                } else {
                    "'little'"
                };

                // Check if source is a slice/array (byte conversion)
                if self.is_byte_sequence_expr(expr) {
                    self.write("int.from_bytes(bytes(");
                    self.generate_expr(expr);
                    self.write("), ");
                    self.write(byte_order);
                    self.write(")");
                    return;
                }

                // Integer to different endian - just mask to the appropriate size
                let native = p.to_native();
                let bits = match native {
                    PrimitiveType::U16 | PrimitiveType::I16 => 16,
                    PrimitiveType::U32 | PrimitiveType::I32 => 32,
                    PrimitiveType::U64 | PrimitiveType::I64 => 64,
                    PrimitiveType::U128 | PrimitiveType::I128 => 128,
                    _ => 32,
                };
                match bits {
                    16 => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & 0xFFFF)");
                    }
                    64 => {
                        self.write("_u64(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    128 => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & ((1 << 128) - 1))");
                    }
                    _ => {
                        self.write("_u32(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                }
                return;
            }
        }

        // Check for integer to byte array cast
        // e.g., value as u8[4] -> value.to_bytes(4, 'big')
        if let TypeKind::Array { element, size } = &ty.kind {
            if let TypeKind::Primitive(PrimitiveType::U8) = &element.kind {
                // Get the endianness from the source expression if it's an endian type
                let byte_order = self.get_expr_endianness(expr);
                self.write("(");
                self.generate_expr(expr);
                self.write(&format!(").to_bytes({}, {})", size, byte_order));
                return;
            }
        }

        // Standard integer casts (masking)
        match &ty.kind {
            TypeKind::Primitive(p) => {
                match p {
                    PrimitiveType::U8 | PrimitiveType::I8 => {
                        self.write("_u8(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & 0xFFFF)");
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        self.write("_u32(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        self.write("_u64(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    PrimitiveType::U128 | PrimitiveType::I128 => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & ((1 << 128) - 1))");
                    }
                    PrimitiveType::Bool => {
                        self.write("bool(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    // Endian types that reach here (shouldn't normally, but fallback)
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
            ExprKind::Index { array, .. } => {
                // array[i] is a single byte, not a sequence
                false
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Paren(inner) => {
                self.is_byte_sequence_expr(inner)
            }
            ExprKind::Ident(_) => {
                // Could be a byte array/slice variable - assume yes for safety
                // The type checker will have validated this
                true
            }
            ExprKind::Field { .. } => true,
            _ => false,
        }
    }

    /// Get the byte order string for an expression based on its type
    fn get_expr_endianness(&self, expr: &Expr) -> &'static str {
        use crate::parser::{TypeKind, Endianness};

        // Check if the expression is a cast to an endian type
        if let ExprKind::Cast { ty, .. } = &expr.kind {
            if let TypeKind::Primitive(p) = &ty.kind {
                return match p.endianness() {
                    Endianness::Big => "'big'",
                    Endianness::Little => "'little'",
                    Endianness::Native => "'little'", // Default to little for native
                };
            }
        }
        // Default to little endian (most common)
        "'little'"
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
}

impl Default for PythonGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for PythonGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();

        // Pre-pass: collect struct field info for read/write generation
        for item in &ast.ast.items {
            match &item.kind {
                ItemKind::Struct(s) => {
                    let fields: Vec<StructFieldInfo> = s.fields.iter().map(|f| StructFieldInfo {
                        name: f.name.name.clone(),
                        ty: f.ty.clone(),
                    }).collect();
                    self.struct_defs.insert(s.name.name.clone(), fields);
                }
                ItemKind::Layout(l) => {
                    let fields: Vec<StructFieldInfo> = l.fields.iter().map(|f| StructFieldInfo {
                        name: f.name.name.clone(),
                        ty: f.ty.clone(),
                    }).collect();
                    self.struct_defs.insert(l.name.name.clone(), fields);
                }
                _ => {}
            }
        }

        self.writeln("# Generated by AlgoC");
        self.writeln("# DO NOT EDIT - This file is auto-generated");
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
            self.writeln("# Test Runner");
            self.writeln("def run_tests():");
            self.indent();
            self.writeln("global _test_failures, _test_name");
            self.writeln("passed = 0");
            self.writeln("failed = 0");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("_test_name = '{}'", name));
                self.writeln("_test_failures = 0");
                self.writeln("try:");
                self.indent();
                self.writeln(&format!("test_{}()", name));
                self.writeln("if _test_failures == 0:");
                self.indent();
                self.writeln(&format!("print('PASS: {}')", name));
                self.writeln("passed += 1");
                self.dedent();
                self.writeln("else:");
                self.indent();
                self.writeln(&format!("print('FAIL: {}')", name));
                self.writeln("failed += 1");
                self.dedent();
                self.dedent();
                self.writeln("except Exception as e:");
                self.indent();
                self.writeln(&format!("print(f'FAIL: {} - {{e}}')", name));
                self.writeln("failed += 1");
                self.dedent();
                self.writeln("");
            }

            self.writeln("print()");
            self.writeln("print(f'{passed} passed, {failed} failed')");
            self.writeln("return failed == 0");
            self.dedent();
            self.writeln("");
        }

        // Main block
        self.writeln("if __name__ == '__main__':");
        self.indent();
        if self.include_tests && !test_names.is_empty() {
            self.writeln("import sys");
            self.writeln("sys.exit(0 if run_tests() else 1)");
        } else {
            self.writeln("pass");
        }
        self.dedent();

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "py"
    }

    fn language_name(&self) -> &'static str {
        "Python"
    }
}

fn escape_py_string(s: &str) -> String {
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
