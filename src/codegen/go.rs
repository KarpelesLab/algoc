//! Go code generator
//!
//! Generates Go code from the analyzed AST.
//! Produces self-contained, compilable Go programs that can be run with `go run`.

use super::CodeGenerator;
use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;
use crate::parser::{
    Ast, BinaryOp, Block, BuiltinFunc, Expr, ExprKind, Function, Item, ItemKind, Stmt, StmtKind,
    Type as ParserType, UnaryOp,
};
use std::collections::{HashMap, HashSet};

/// Struct field info for code generation
#[derive(Clone)]
struct StructFieldInfo {
    name: String,
    ty: ParserType,
}

/// Struct method info (method name -> mangled function name)
type MethodMap = HashMap<String, String>;

/// Go code generator
pub struct GoGenerator {
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
    /// Track which imports are needed
    needed_imports: HashSet<String>,
    /// Whether we need the assert helper
    needs_assert: bool,
    /// Whether we need the bytes_equal helper
    needs_bytes_equal: bool,
    /// Whether we need the conditional helper functions (one per type)
    needs_cond_uint8: bool,
    needs_cond_uint16: bool,
    needs_cond_uint32: bool,
    needs_cond_uint64: bool,
    needs_cond_bool: bool,
    needs_cond_bytes: bool,
    /// Whether we need the constant_time_eq helper
    needs_constant_time_eq: bool,
}

impl GoGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            needed_imports: HashSet::new(),
            needs_assert: false,
            needs_bytes_equal: false,
            needs_cond_uint8: false,
            needs_cond_uint16: false,
            needs_cond_uint32: false,
            needs_cond_uint64: false,
            needs_cond_bool: false,
            needs_cond_bytes: false,
            needs_constant_time_eq: false,
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
            self.output.push('\t');
        }
    }

    fn indent(&mut self) {
        self.indent += 1;
    }

    fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    /// Map an AlgoC type to a Go type string
    #[allow(clippy::only_used_in_recursion)]
    fn go_type(&self, ty: &ParserType) -> String {
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => "uint8".to_string(),
                    PrimitiveType::U16 | PrimitiveType::I16 => "uint16".to_string(),
                    PrimitiveType::U32 | PrimitiveType::I32 => "uint32".to_string(),
                    PrimitiveType::U64 | PrimitiveType::I64 => "uint64".to_string(),
                    PrimitiveType::U128 | PrimitiveType::I128 => "[2]uint64".to_string(),
                    PrimitiveType::Bool => "bool".to_string(),
                    _ => "uint32".to_string(),
                }
            }
            TypeKind::Array { element, size } => {
                format!("[{}]{}", size, self.go_type(element))
            }
            TypeKind::Slice { element } => {
                format!("[]{}", self.go_type(element))
            }
            TypeKind::ArrayRef { element, .. } => {
                format!("[]{}", self.go_type(element))
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.go_type(inner),
            TypeKind::Named(ident) => ident.name.clone(),
            TypeKind::SelfType => "interface{}".to_string(),
        }
    }

    /// Get the default value expression for a Go type
    #[allow(dead_code)]
    fn default_value_for_type(&self, ty: &ParserType) -> String {
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::Bool => "false".to_string(),
                    PrimitiveType::U128 | PrimitiveType::I128 => "[2]uint64{0, 0}".to_string(),
                    _ => "0".to_string(),
                }
            }
            TypeKind::Array { element, size } => {
                let elem_default = self.default_value_for_type(element);
                // For arrays, Go zero-initializes by default
                match &element.kind {
                    TypeKind::Primitive(_) => {
                        format!("[{}]{}{{}}", size, self.go_type(element))
                    }
                    _ => {
                        // Need to fill with default values
                        let go_elem = self.go_type(element);
                        format!(
                            "func() [{}]{} {{ var a [{}]{}; for i := range a {{ a[i] = {} }}; return a }}()",
                            size, go_elem, size, go_elem, elem_default
                        )
                    }
                }
            }
            TypeKind::Slice { element } => {
                format!("[]{}{{}}", self.go_type(element))
            }
            TypeKind::Named(ident) => {
                format!("{}{{}}", ident.name)
            }
            _ => "nil".to_string(),
        }
    }

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        // Reader struct and methods
        self.writeln("// Reader provides streaming byte input");
        self.writeln("type Reader struct {");
        self.indent();
        self.writeln("data []byte");
        self.writeln("pos  int");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("func NewReader(data []byte) *Reader {");
        self.indent();
        self.writeln("return &Reader{data: data, pos: 0}");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u8
        self.writeln("func (r *Reader) read_u8() uint8 {");
        self.indent();
        self.writeln("if r.pos >= len(r.data) {");
        self.indent();
        self.writeln("panic(\"EOF\")");
        self.dedent();
        self.writeln("}");
        self.writeln("v := r.data[r.pos]");
        self.writeln("r.pos++");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u16be / read_u16le / read_u16
        for (method, order) in [
            ("read_u16be", "BigEndian"),
            ("read_u16le", "LittleEndian"),
            ("read_u16", "BigEndian"),
        ] {
            self.writeln(&format!("func (r *Reader) {}() uint16 {{", method));
            self.indent();
            self.writeln("if r.pos+2 > len(r.data) {");
            self.indent();
            self.writeln("panic(\"EOF\")");
            self.dedent();
            self.writeln("}");
            self.writeln(&format!("v := binary.{}.Uint16(r.data[r.pos:])", order));
            self.writeln("r.pos += 2");
            self.writeln("return v");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // read_u32be / read_u32le / read_u32
        for (method, order) in [
            ("read_u32be", "BigEndian"),
            ("read_u32le", "LittleEndian"),
            ("read_u32", "BigEndian"),
        ] {
            self.writeln(&format!("func (r *Reader) {}() uint32 {{", method));
            self.indent();
            self.writeln("if r.pos+4 > len(r.data) {");
            self.indent();
            self.writeln("panic(\"EOF\")");
            self.dedent();
            self.writeln("}");
            self.writeln(&format!("v := binary.{}.Uint32(r.data[r.pos:])", order));
            self.writeln("r.pos += 4");
            self.writeln("return v");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // read_u64be / read_u64le / read_u64
        for (method, order) in [
            ("read_u64be", "BigEndian"),
            ("read_u64le", "LittleEndian"),
            ("read_u64", "BigEndian"),
        ] {
            self.writeln(&format!("func (r *Reader) {}() uint64 {{", method));
            self.indent();
            self.writeln("if r.pos+8 > len(r.data) {");
            self.indent();
            self.writeln("panic(\"EOF\")");
            self.dedent();
            self.writeln("}");
            self.writeln(&format!("v := binary.{}.Uint64(r.data[r.pos:])", order));
            self.writeln("r.pos += 8");
            self.writeln("return v");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // read_bytes
        self.writeln("func (r *Reader) read_bytes(count int) []byte {");
        self.indent();
        self.writeln("if r.pos+count > len(r.data) {");
        self.indent();
        self.writeln("panic(\"EOF\")");
        self.dedent();
        self.writeln("}");
        self.writeln("result := make([]byte, count)");
        self.writeln("copy(result, r.data[r.pos:r.pos+count])");
        self.writeln("r.pos += count");
        self.writeln("return result");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_chunk
        self.writeln("func (r *Reader) read_chunk(maxSize int) []byte {");
        self.indent();
        self.writeln("remaining := len(r.data) - r.pos");
        self.writeln("count := maxSize");
        self.writeln("if remaining < count {");
        self.indent();
        self.writeln("count = remaining");
        self.dedent();
        self.writeln("}");
        self.writeln("result := make([]byte, count)");
        self.writeln("copy(result, r.data[r.pos:r.pos+count])");
        self.writeln("r.pos += count");
        self.writeln("return result");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // eof
        self.writeln("func (r *Reader) eof() bool {");
        self.indent();
        self.writeln("return r.pos >= len(r.data)");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer struct and methods
        self.writeln("// Writer provides streaming byte output");
        self.writeln("type Writer struct {");
        self.indent();
        self.writeln("data []byte");
        self.writeln("pos  int");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("func NewWriter(data []byte) *Writer {");
        self.indent();
        self.writeln("return &Writer{data: data, pos: 0}");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u8
        self.writeln("func (w *Writer) write_u8(v uint8) {");
        self.indent();
        self.writeln("if w.pos >= len(w.data) {");
        self.indent();
        self.writeln("panic(\"Buffer overflow\")");
        self.dedent();
        self.writeln("}");
        self.writeln("w.data[w.pos] = v");
        self.writeln("w.pos++");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u16be / write_u16le / write_u16
        for (method, order) in [
            ("write_u16be", "BigEndian"),
            ("write_u16le", "LittleEndian"),
            ("write_u16", "BigEndian"),
        ] {
            self.writeln(&format!("func (w *Writer) {}(v uint16) {{", method));
            self.indent();
            self.writeln("if w.pos+2 > len(w.data) {");
            self.indent();
            self.writeln("panic(\"Buffer overflow\")");
            self.dedent();
            self.writeln("}");
            self.writeln(&format!("binary.{}.PutUint16(w.data[w.pos:], v)", order));
            self.writeln("w.pos += 2");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // write_u32be / write_u32le / write_u32
        for (method, order) in [
            ("write_u32be", "BigEndian"),
            ("write_u32le", "LittleEndian"),
            ("write_u32", "BigEndian"),
        ] {
            self.writeln(&format!("func (w *Writer) {}(v uint32) {{", method));
            self.indent();
            self.writeln("if w.pos+4 > len(w.data) {");
            self.indent();
            self.writeln("panic(\"Buffer overflow\")");
            self.dedent();
            self.writeln("}");
            self.writeln(&format!("binary.{}.PutUint32(w.data[w.pos:], v)", order));
            self.writeln("w.pos += 4");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // write_u64be / write_u64le / write_u64
        for (method, order) in [
            ("write_u64be", "BigEndian"),
            ("write_u64le", "LittleEndian"),
            ("write_u64", "BigEndian"),
        ] {
            self.writeln(&format!("func (w *Writer) {}(v uint64) {{", method));
            self.indent();
            self.writeln("if w.pos+8 > len(w.data) {");
            self.indent();
            self.writeln("panic(\"Buffer overflow\")");
            self.dedent();
            self.writeln("}");
            self.writeln(&format!("binary.{}.PutUint64(w.data[w.pos:], v)", order));
            self.writeln("w.pos += 8");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // write_bytes
        self.writeln("func (w *Writer) write_bytes(data []byte) {");
        self.indent();
        self.writeln("if w.pos+len(data) > len(w.data) {");
        self.indent();
        self.writeln("panic(\"Buffer overflow\")");
        self.dedent();
        self.writeln("}");
        self.writeln("copy(w.data[w.pos:], data)");
        self.writeln("w.pos += len(data)");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Generate helper functions that are conditionally needed
    fn generate_helpers(&mut self) {
        if self.needs_assert {
            self.writeln("var __test_failures int");
            self.writeln("var __test_name string");
            self.writeln("");
            self.writeln("func __assert(condition bool) {");
            self.indent();
            self.writeln("if !condition {");
            self.indent();
            self.writeln("__test_failures++");
            self.writeln("fmt.Println(\"  ASSERTION FAILED in \" + __test_name)");
            self.dedent();
            self.writeln("}");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        if self.needs_bytes_equal {
            self.writeln("func __bytes_equal(a, b []byte) bool {");
            self.indent();
            self.writeln("if len(a) != len(b) {");
            self.indent();
            self.writeln("return false");
            self.dedent();
            self.writeln("}");
            self.writeln("for i := range a {");
            self.indent();
            self.writeln("if a[i] != b[i] {");
            self.indent();
            self.writeln("return false");
            self.dedent();
            self.writeln("}");
            self.dedent();
            self.writeln("}");
            self.writeln("return true");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        if self.needs_constant_time_eq {
            self.writeln("func constant_time_eq(a, b []byte) bool {");
            self.indent();
            self.writeln("if len(a) != len(b) {");
            self.indent();
            self.writeln("return false");
            self.dedent();
            self.writeln("}");
            self.writeln("var v byte");
            self.writeln("for i := range a {");
            self.indent();
            self.writeln("v |= a[i] ^ b[i]");
            self.dedent();
            self.writeln("}");
            self.writeln("return v == 0");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // Conditional helper functions (Go has no ternary operator)
        if self.needs_cond_uint8 {
            self.writeln("func __cond_uint8(c bool, a, b uint8) uint8 {");
            self.indent();
            self.writeln("if c {");
            self.indent();
            self.writeln("return a");
            self.dedent();
            self.writeln("}");
            self.writeln("return b");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        if self.needs_cond_uint16 {
            self.writeln("func __cond_uint16(c bool, a, b uint16) uint16 {");
            self.indent();
            self.writeln("if c {");
            self.indent();
            self.writeln("return a");
            self.dedent();
            self.writeln("}");
            self.writeln("return b");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        if self.needs_cond_uint32 {
            self.writeln("func __cond_uint32(c bool, a, b uint32) uint32 {");
            self.indent();
            self.writeln("if c {");
            self.indent();
            self.writeln("return a");
            self.dedent();
            self.writeln("}");
            self.writeln("return b");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        if self.needs_cond_uint64 {
            self.writeln("func __cond_uint64(c bool, a, b uint64) uint64 {");
            self.indent();
            self.writeln("if c {");
            self.indent();
            self.writeln("return a");
            self.dedent();
            self.writeln("}");
            self.writeln("return b");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        if self.needs_cond_bool {
            self.writeln("func __cond_bool(c bool, a, b bool) bool {");
            self.indent();
            self.writeln("if c {");
            self.indent();
            self.writeln("return a");
            self.dedent();
            self.writeln("}");
            self.writeln("return b");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        if self.needs_cond_bytes {
            self.writeln("func __cond_bytes(c bool, a, b []byte) []byte {");
            self.indent();
            self.writeln("if c {");
            self.indent();
            self.writeln("return a");
            self.dedent();
            self.writeln("}");
            self.writeln("return b");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }
    }

    /// Pre-scan the AST to determine which imports and helpers are needed
    fn pre_scan_ast(&mut self, ast: &Ast) {
        for item in &ast.items {
            self.pre_scan_item(item);
        }
    }

    fn pre_scan_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => self.pre_scan_block(&func.body),
            ItemKind::Impl(impl_def) => {
                for method in &impl_def.methods {
                    self.pre_scan_block(&method.body);
                }
            }
            ItemKind::Test(test) => {
                if self.include_tests {
                    self.needs_assert = true;
                    self.needed_imports.insert("fmt".to_string());
                    self.pre_scan_block(&test.body);
                }
            }
            ItemKind::Const(c) => self.pre_scan_expr(&c.value),
            _ => {}
        }
    }

    fn pre_scan_block(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.pre_scan_stmt(stmt);
        }
    }

    fn pre_scan_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let {
                init: Some(expr), ..
            } => {
                self.pre_scan_expr(expr);
            }
            StmtKind::Expr(expr) => self.pre_scan_expr(expr),
            StmtKind::Assign { target, value } => {
                self.pre_scan_expr(target);
                self.pre_scan_expr(value);
            }
            StmtKind::CompoundAssign { target, value, .. } => {
                self.pre_scan_expr(target);
                self.pre_scan_expr(value);
            }
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.pre_scan_expr(condition);
                self.pre_scan_block(then_block);
                if let Some(eb) = else_block {
                    self.pre_scan_block(eb);
                }
            }
            StmtKind::For {
                start, end, body, ..
            } => {
                self.pre_scan_expr(start);
                self.pre_scan_expr(end);
                self.pre_scan_block(body);
            }
            StmtKind::While { condition, body } => {
                self.pre_scan_expr(condition);
                self.pre_scan_block(body);
            }
            StmtKind::Loop { body } => self.pre_scan_block(body),
            StmtKind::Return(Some(expr)) => self.pre_scan_expr(expr),
            StmtKind::Block(block) => self.pre_scan_block(block),
            _ => {}
        }
    }

    fn pre_scan_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Builtin {
                name: BuiltinFunc::Assert,
                ..
            } => {
                self.needs_assert = true;
                self.needed_imports.insert("fmt".to_string());
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.pre_scan_expr(inner);
                // Endian casts need encoding/binary
                if let crate::parser::TypeKind::Primitive(p) = &ty.kind
                    && p.endianness() != crate::parser::Endianness::Native
                    && is_byte_sequence_expr(inner)
                {
                    self.needed_imports.insert("encoding/binary".to_string());
                }
            }
            ExprKind::Binary { left, op, right } => {
                self.pre_scan_expr(left);
                self.pre_scan_expr(right);
                // Array equality comparisons need __bytes_equal or constant_time_eq
                if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
                    let left_is_array = is_array_like_expr(left);
                    let right_is_array = is_array_like_expr(right);
                    if left_is_array || right_is_array {
                        self.needs_constant_time_eq = true;
                    }
                }
            }
            ExprKind::Unary { operand, .. } => self.pre_scan_expr(operand),
            ExprKind::Index { array, index } => {
                self.pre_scan_expr(array);
                self.pre_scan_expr(index);
            }
            ExprKind::Slice {
                array, start, end, ..
            } => {
                self.pre_scan_expr(array);
                self.pre_scan_expr(start);
                self.pre_scan_expr(end);
            }
            ExprKind::Field { object, .. } => self.pre_scan_expr(object),
            ExprKind::Call { func, args } => {
                self.pre_scan_expr(func);
                for arg in args {
                    self.pre_scan_expr(arg);
                }
                // Check for Reader/Writer creation which needs encoding/binary
                if let ExprKind::Ident(ident) = &func.kind
                    && (ident.name == "Reader" || ident.name == "Writer")
                {
                    self.needed_imports.insert("encoding/binary".to_string());
                }
                // Check for reader/writer method calls
                if let ExprKind::Field { field, .. } = &func.kind {
                    let reader_writer_methods = [
                        "read_u16",
                        "read_u16be",
                        "read_u16le",
                        "read_u32",
                        "read_u32be",
                        "read_u32le",
                        "read_u64",
                        "read_u64be",
                        "read_u64le",
                        "write_u16",
                        "write_u16be",
                        "write_u16le",
                        "write_u32",
                        "write_u32be",
                        "write_u32le",
                        "write_u64",
                        "write_u64be",
                        "write_u64le",
                    ];
                    if reader_writer_methods.contains(&field.name.as_str()) {
                        self.needed_imports.insert("encoding/binary".to_string());
                    }
                }
            }
            ExprKind::Array(elems) => {
                for e in elems {
                    self.pre_scan_expr(e);
                }
            }
            ExprKind::ArrayRepeat { value, count } => {
                self.pre_scan_expr(value);
                self.pre_scan_expr(count);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Deref(inner) => {
                self.pre_scan_expr(inner);
            }
            ExprKind::Paren(inner) => self.pre_scan_expr(inner),
            ExprKind::StructLit { fields, .. } => {
                for (_, value) in fields {
                    self.pre_scan_expr(value);
                }
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                self.pre_scan_expr(condition);
                self.pre_scan_expr(then_expr);
                self.pre_scan_expr(else_expr);
                // Mark that we need a conditional helper - use uint32 as default
                self.needs_cond_uint32 = true;
            }
            ExprKind::EnumVariant { args, .. } => {
                for arg in args {
                    self.pre_scan_expr(arg);
                }
            }
            ExprKind::Match { expr: inner, arms } => {
                self.pre_scan_expr(inner);
                for arm in arms {
                    self.pre_scan_expr(&arm.body);
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                self.pre_scan_expr(receiver);
                for arg in args {
                    self.pre_scan_expr(arg);
                }
            }
            ExprKind::TypeStaticCall { args, .. } => {
                for arg in args {
                    self.pre_scan_expr(arg);
                }
            }
            ExprKind::GenericCall { func, args, .. } => {
                self.pre_scan_expr(func);
                for arg in args {
                    self.pre_scan_expr(arg);
                }
            }
            ExprKind::Range { start, end, .. } => {
                self.pre_scan_expr(start);
                self.pre_scan_expr(end);
            }
            _ => {}
        }
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

    fn generate_function(&mut self, func: &Function) {
        self.write_indent();
        self.write(&format!("func {}(", func.name.name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&format!("{} {}", param.name.name, self.go_type(&param.ty)));
        }

        self.write(")");

        // Return type
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!(" {}", self.go_type(ret_ty)));
        }

        self.write(" {\n");
        self.indent();
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_method(&mut self, struct_name: &str, func: &Function) {
        let mangled_name = format!("{}__{}", struct_name, func.name.name);

        self.write_indent();
        self.write(&format!("func {}(", mangled_name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&format!("{} {}", param.name.name, self.go_type(&param.ty)));
        }

        self.write(")");

        // Return type
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!(" {}", self.go_type(ret_ty)));
        }

        self.write(" {\n");
        self.indent();
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("func test_{}() {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        self.write(&format!("var {} = ", c.name.name));
        self.generate_expr(&c.value);
        self.write("\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        self.writeln(&format!("type {} struct {{", s.name.name));
        self.indent();
        for field in &s.fields {
            self.writeln(&format!(
                "{} {}",
                go_exported_field(&field.name.name),
                self.go_type(&field.ty)
            ));
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        self.writeln(&format!("type {} struct {{", l.name.name));
        self.indent();
        for field in &l.fields {
            self.writeln(&format!(
                "{} {}",
                go_exported_field(&field.name.name),
                self.go_type(&field.ty)
            ));
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        let enum_name = &e.name.name;

        // Generate the enum struct with a tag field and value fields
        self.writeln(&format!("type {} struct {{", enum_name));
        self.indent();
        self.writeln("Tag string");

        // Collect all possible value fields from all variants
        let mut has_tuple_fields = false;
        let mut max_tuple_fields = 0;
        let mut has_struct_fields = false;
        let mut struct_field_names: Vec<String> = Vec::new();

        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {}
                crate::parser::EnumVariantData::Tuple(types) => {
                    has_tuple_fields = true;
                    if types.len() > max_tuple_fields {
                        max_tuple_fields = types.len();
                    }
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    has_struct_fields = true;
                    for f in fields {
                        if !struct_field_names.contains(&f.name.name) {
                            struct_field_names.push(f.name.name.clone());
                        }
                    }
                }
            }
        }

        if has_tuple_fields {
            for i in 0..max_tuple_fields {
                // Use interface{} for variant fields since types may differ
                self.writeln(&format!("V{} interface{{}}", i));
            }
        }
        if has_struct_fields {
            for name in &struct_field_names {
                self.writeln(&format!("{} interface{{}}", go_exported_field(name)));
            }
        }

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Generate constructor functions for each variant
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!(
                        "var {}_{} = {}{{Tag: \"{}\"}}",
                        enum_name, variant.name.name, enum_name, variant.name.name
                    ));
                    self.writeln("");
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    let params: Vec<String> = (0..types.len())
                        .map(|i| format!("v{} interface{{}}", i))
                        .collect();
                    self.writeln(&format!(
                        "func {}_{}({}) {} {{",
                        enum_name,
                        variant.name.name,
                        params.join(", "),
                        enum_name
                    ));
                    self.indent();
                    self.write_indent();
                    self.write(&format!(
                        "return {}{{Tag: \"{}\"",
                        enum_name, variant.name.name
                    ));
                    for i in 0..types.len() {
                        self.write(&format!(", V{}: v{}", i, i));
                    }
                    self.write("}\n");
                    self.dedent();
                    self.writeln("}");
                    self.writeln("");
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    let params: Vec<String> = fields
                        .iter()
                        .map(|f| format!("{} interface{{}}", f.name.name))
                        .collect();
                    self.writeln(&format!(
                        "func {}_{}({}) {} {{",
                        enum_name,
                        variant.name.name,
                        params.join(", "),
                        enum_name
                    ));
                    self.indent();
                    self.write_indent();
                    self.write(&format!(
                        "return {}{{Tag: \"{}\"",
                        enum_name, variant.name.name
                    ));
                    for f in fields {
                        self.write(&format!(
                            ", {}: {}",
                            go_exported_field(&f.name.name),
                            f.name.name
                        ));
                    }
                    self.write("}\n");
                    self.dedent();
                    self.writeln("}");
                    self.writeln("");
                }
            }
        }
    }

    fn generate_block(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.generate_stmt(stmt);
        }
    }

    fn generate_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let { name, ty, init, .. } => {
                // Track struct types for read/write generation
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

                if let Some(init) = init {
                    // Use := for variable declaration with initialization
                    self.write_indent();
                    self.write(&format!("{} := ", name.name));
                    self.generate_expr(init);
                    self.write("\n");
                } else if let Some(ty) = ty {
                    // Use var for declaration without initialization
                    self.write_indent();
                    let go_ty = self.go_type(ty);
                    self.write(&format!("var {} {}\n", name.name, go_ty));
                } else {
                    // No type, no init - shouldn't happen but handle gracefully
                    self.write_indent();
                    self.write(&format!("var {} interface{{}}\n", name.name));
                }
            }
            StmtKind::Expr(expr) => {
                // Check if this is a call expression - if so, don't discard result
                // For Go, we need to handle unused returns carefully
                self.write_indent();
                // If the expression is a function call that returns void, it's fine.
                // If it returns a value, Go will complain about unused value, but
                // as a statement the result is already discarded.
                self.generate_expr(expr);
                self.write("\n");
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
                        let order = if endian == crate::parser::Endianness::Little {
                            "LittleEndian"
                        } else {
                            "BigEndian"
                        };
                        let native = p.to_native();
                        let (put_fn, byte_count) = match native {
                            crate::parser::PrimitiveType::U16
                            | crate::parser::PrimitiveType::I16 => ("PutUint16", 2usize),
                            crate::parser::PrimitiveType::U32
                            | crate::parser::PrimitiveType::I32 => ("PutUint32", 4),
                            crate::parser::PrimitiveType::U64
                            | crate::parser::PrimitiveType::I64 => ("PutUint64", 8),
                            _ => ("PutUint32", 4),
                        };
                        self.needed_imports.insert("encoding/binary".to_string());
                        self.write_indent();
                        self.write(&format!("binary.{}.{}(", order, put_fn));
                        self.generate_expr(array);
                        self.write("[");
                        self.generate_expr(start);
                        self.write(":");
                        self.generate_expr(end);
                        self.write("], ");
                        let _ = byte_count; // used conceptually for the type
                        let cast_type = match native {
                            crate::parser::PrimitiveType::U16
                            | crate::parser::PrimitiveType::I16 => "uint16",
                            crate::parser::PrimitiveType::U64
                            | crate::parser::PrimitiveType::I64 => "uint64",
                            _ => "uint32",
                        };
                        self.write(&format!("{}(", cast_type));
                        self.generate_expr(value);
                        self.write("))\n");
                        return;
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
                    BinaryOp::Div => " /= ",
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
                self.write(&format!("for {} := ", var.name));
                self.generate_expr(start);
                self.write(&format!(
                    "; {} {} ",
                    var.name,
                    if *inclusive { "<=" } else { "<" }
                ));
                self.generate_expr(end);
                self.write(&format!("; {}++ {{\n", var.name));
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::While { condition, body } => {
                self.write_indent();
                self.write("for ");
                self.generate_expr(condition);
                self.write(" {\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::Loop { body } => {
                self.writeln("for {");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::Break => {
                self.writeln("break");
            }
            StmtKind::Continue => {
                self.writeln("continue");
            }
            StmtKind::Return(expr) => {
                self.write_indent();
                self.write("return");
                if let Some(expr) = expr {
                    self.write(" ");
                    self.generate_expr(expr);
                }
                self.write("\n");
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
                // Convert string to []byte
                self.write(&format!("[]byte(\"{}\")", escape_go_string(s)));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("[]byte(\"{}\")", escape_go_string(s)));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to []byte literal
                let bytes: Vec<String> = (0..h.len() / 2)
                    .map(|i| format!("0x{}", &h[i * 2..i * 2 + 2]))
                    .collect();
                self.write(&format!("[]byte{{{}}}", bytes.join(", ")));
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                // For array comparisons, use constant_time_eq
                if matches!(op, BinaryOp::Eq | BinaryOp::Ne) {
                    let left_is_array = is_array_like_expr(left);
                    let right_is_array = is_array_like_expr(right);

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

                self.write("(");
                self.generate_expr(left);
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
                    BinaryOp::Shr => " >> ",
                    BinaryOp::Eq => " == ",
                    BinaryOp::Ne => " != ",
                    BinaryOp::Lt => " < ",
                    BinaryOp::Le => " <= ",
                    BinaryOp::Gt => " > ",
                    BinaryOp::Ge => " >= ",
                    BinaryOp::And => " && ",
                    BinaryOp::Or => " || ",
                };
                self.write(op_str);
                self.generate_expr(right);
                self.write(")");
            }
            ExprKind::Unary { op, operand } => {
                let op_str = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "!",
                    UnaryOp::BitNot => "^", // Go uses ^ for bitwise NOT
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
                self.write("]");
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
                self.write(":");
                if *inclusive {
                    self.generate_expr(end);
                    self.write("+1");
                } else {
                    self.generate_expr(end);
                }
                self.write("]");
            }
            ExprKind::Field { object, field } => {
                self.generate_expr(object);
                self.write(&format!(".{}", go_exported_field(&field.name)));
            }
            ExprKind::Call { func, args } => {
                // Check for Reader/Writer constructor calls
                if let ExprKind::Ident(ident) = &func.kind {
                    if ident.name == "Reader" {
                        self.write("NewReader(");
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_expr(arg);
                        }
                        self.write(")");
                        return;
                    }
                    if ident.name == "Writer" {
                        self.write("NewWriter(");
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
                        // Convert .len() to len(slice)
                        self.write("len(");
                        self.generate_expr(object);
                        self.write(")");
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
                        self.write("func() { ");
                        for field_info in &fields {
                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty)
                            {
                                self.write(&format!(
                                    "{}.{} = ",
                                    var_ident.name,
                                    go_exported_field(&field_info.name)
                                ));
                                self.generate_expr(object);
                                self.write(&format!(".{}(); ", read_method));
                            }
                        }
                        self.write("}()");
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
                            self.write("func() { ");
                            for field_info in &fields {
                                if let Some(write_method) =
                                    self.get_write_method_for_type(&field_info.ty)
                                {
                                    self.generate_expr(object);
                                    self.write(&format!(
                                        ".{}({}.{}); ",
                                        write_method,
                                        var_ident.name,
                                        go_exported_field(&field_info.name)
                                    ));
                                }
                            }
                            self.write("}()");
                            return;
                        }
                    }

                    // Reader/Writer method calls - pass through as method calls
                    let reader_methods = [
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
                    ];
                    let writer_methods = [
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
                    if reader_methods.contains(&field.name.as_str())
                        || writer_methods.contains(&field.name.as_str())
                    {
                        self.generate_expr(object);
                        self.write(&format!(".{}(", field.name));
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            // For read_bytes/read_chunk, cast arg to int
                            if (field.name == "read_bytes" || field.name == "read_chunk") && i == 0
                            {
                                self.write("int(");
                                self.generate_expr(arg);
                                self.write(")");
                            } else {
                                self.generate_expr(arg);
                            }
                        }
                        self.write(")");
                        return;
                    }

                    // Check for struct method calls (object.method(args))
                    if let ExprKind::Ident(obj_ident) = &object.kind
                        && let Some(struct_name) = self.var_types.get(&obj_ident.name).cloned()
                        && let Some(methods) = self.struct_methods.get(&struct_name).cloned()
                        && let Some(mangled_name) = methods.get(&field.name)
                    {
                        // Generate: StructName__method(object, args...)
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
                    self.write("[]byte{}");
                } else {
                    // Check if all elements are small integers (bytes)
                    let all_bytes = elements.iter().all(|e| {
                        if let ExprKind::Integer(n) = &e.kind {
                            *n <= 255
                        } else {
                            false
                        }
                    });

                    if all_bytes {
                        self.write("[]byte{");
                    } else {
                        self.write("[]uint32{");
                    }
                    for (i, elem) in elements.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(elem);
                    }
                    self.write("}");
                }
            }
            ExprKind::ArrayRepeat { value, count } => {
                // In Go, we need to create a slice and fill it
                let is_byte = is_byte_value(value);
                if is_byte {
                    // For byte arrays, create with make and fill
                    self.write("func() []byte { s := make([]byte, ");
                    self.generate_expr(count);
                    self.write("); for i := range s { s[i] = ");
                    self.generate_expr(value);
                    self.write(" }; return s }()");
                } else {
                    self.write("func() []uint32 { s := make([]uint32, ");
                    self.generate_expr(count);
                    self.write("); for i := range s { s[i] = ");
                    self.generate_expr(value);
                    self.write(" }; return s }()");
                }
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in Go - for slices they're already references,
                // for other types we just pass the value
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are typically no-ops for our usage
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
            ExprKind::StructLit { name, fields } => {
                self.write(&format!("{}{{", name.name));
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("{}: ", go_exported_field(&field_name.name)));
                    self.generate_expr(value);
                }
                self.write("}");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // Go has no ternary operator - use helper function
                // We use a generic approach with a helper function
                self.write("__cond_uint32(");
                self.generate_expr(condition);
                self.write(", ");
                self.generate_expr(then_expr);
                self.write(", ");
                self.generate_expr(else_expr);
                self.write(")");
            }
            ExprKind::EnumVariant {
                enum_name,
                variant_name,
                args,
            } => {
                if args.is_empty() {
                    self.write(&format!("{}_{}", enum_name.name, variant_name.name));
                } else {
                    self.write(&format!("{}_{}(", enum_name.name, variant_name.name));
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
                // Generate match as an IIFE with switch on tag
                self.write("func() interface{} { __match := ");
                self.generate_expr(expr);
                self.write("; ");
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write(" else ");
                    }
                    self.generate_pattern_match(&arm.pattern, "__match");
                    self.write(" { return ");
                    self.generate_expr(&arm.body);
                    self.write("; }");
                }
                self.write("; return nil }()");
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

    fn generate_pattern_match(&mut self, pattern: &crate::parser::Pattern, scrutinee: &str) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("if true");
            }
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("if {} == ", scrutinee));
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(ident) => {
                // Binding pattern - always matches, bind the value
                // In Go, we use a local scope
                self.write(&format!(
                    "if func() bool {{ {} := {}; _ = {}; return true }}()",
                    ident.name, scrutinee, ident.name
                ));
            }
            PatternKind::EnumVariant {
                variant_name,
                bindings,
                ..
            } => {
                self.write(&format!(
                    "if {}.Tag == \"{}\"",
                    scrutinee, variant_name.name
                ));
                // Bindings are handled in the body
                let _ = bindings;
            }
            PatternKind::Tuple(_patterns) => {
                self.write("if true"); // Simplified
            }
            PatternKind::Or(patterns) => {
                self.write("if ");
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

    fn generate_pattern_condition(&mut self, pattern: &crate::parser::Pattern, scrutinee: &str) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => self.write("true"),
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("{} == ", scrutinee));
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(_) => self.write("true"),
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!("{}.Tag == \"{}\"", scrutinee, variant_name.name));
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

    fn generate_builtin(&mut self, name: BuiltinFunc, args: &[Expr]) {
        match name {
            BuiltinFunc::Assert => {
                self.write("__assert(");
                self.generate_expr(&args[0]);
                self.write(")");
            }
        }
    }

    fn generate_cast(&mut self, expr: &Expr, ty: &ParserType) {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        // Check for endian byte conversions (byte slice/array to integer)
        if let TypeKind::Primitive(p) = &ty.kind {
            let endian = p.endianness();
            if endian != Endianness::Native {
                let native = p.to_native();

                // Check if source is a slice/array (byte conversion)
                if is_byte_sequence_expr(expr) {
                    self.needed_imports.insert("encoding/binary".to_string());
                    let order = if endian == Endianness::Little {
                        "LittleEndian"
                    } else {
                        "BigEndian"
                    };

                    match native {
                        PrimitiveType::U16 | PrimitiveType::I16 => {
                            self.write(&format!("binary.{}.Uint16(", order));
                            self.generate_expr(expr);
                            self.write(")");
                        }
                        PrimitiveType::U32 | PrimitiveType::I32 => {
                            self.write(&format!("binary.{}.Uint32(", order));
                            self.generate_expr(expr);
                            self.write(")");
                        }
                        PrimitiveType::U64 | PrimitiveType::I64 => {
                            self.write(&format!("binary.{}.Uint64(", order));
                            self.generate_expr(expr);
                            self.write(")");
                        }
                        PrimitiveType::U128 | PrimitiveType::I128 => {
                            // Manual 128-bit from bytes
                            let little = endian == Endianness::Little;
                            self.write("func() [2]uint64 { __b := ");
                            self.generate_expr(expr);
                            self.write("; ");
                            if little {
                                self.write("return [2]uint64{binary.LittleEndian.Uint64(__b[8:]), binary.LittleEndian.Uint64(__b[0:8])}");
                            } else {
                                self.write("return [2]uint64{binary.BigEndian.Uint64(__b[0:8]), binary.BigEndian.Uint64(__b[8:])}");
                            }
                            self.write(" }()");
                        }
                        _ => {
                            self.write(&format!("binary.{}.Uint32(", order));
                            self.generate_expr(expr);
                            self.write(")");
                        }
                    }
                    return;
                }

                // Integer to integer with different endianness - just cast/mask
                match native {
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        self.write("uint16(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        self.write("uint32(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        self.write("uint64(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    _ => {
                        self.write("uint32(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                }
                return;
            }
        }

        // Check for integer to byte array cast
        if let TypeKind::Array { element, size } = &ty.kind
            && let TypeKind::Primitive(PrimitiveType::U8) = &element.kind
        {
            let (little_endian, bits) = self.get_expr_endianness_info(expr);
            self.needed_imports.insert("encoding/binary".to_string());

            if bits <= 64 {
                let order = if little_endian {
                    "LittleEndian"
                } else {
                    "BigEndian"
                };
                let put_fn = match bits {
                    16 => "PutUint16",
                    64 => "PutUint64",
                    _ => "PutUint32",
                };
                let cast_type = match bits {
                    16 => "uint16",
                    64 => "uint64",
                    _ => "uint32",
                };

                self.write(&format!(
                    "func() []byte {{ __a := make([]byte, {}); binary.{}.{}(__a, {}(",
                    size, order, put_fn, cast_type
                ));
                self.generate_expr(expr);
                self.write(")); return __a }()");
            } else {
                // 128-bit
                let inner_expr = if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                    inner
                } else {
                    expr
                };
                let order = if little_endian {
                    "LittleEndian"
                } else {
                    "BigEndian"
                };
                self.write("func() []byte { __v := ");
                self.generate_expr(inner_expr);
                self.write(&format!(
                        "; __a := make([]byte, 16); binary.{}.PutUint64(__a[0:8], __v[0]); binary.{}.PutUint64(__a[8:16], __v[1]); return __a }}()",
                        order, order
                    ));
            }
            return;
        }

        // Standard casts - Go type conversions
        match &ty.kind {
            TypeKind::Primitive(p) => match p {
                PrimitiveType::U8 | PrimitiveType::I8 => {
                    self.write("uint8(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::U16 | PrimitiveType::I16 => {
                    self.write("uint16(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::U32 | PrimitiveType::I32 => {
                    self.write("uint32(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::U64 | PrimitiveType::I64 => {
                    self.write("uint64(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::U128 | PrimitiveType::I128 => {
                    // u128 is [2]uint64 - convert from smaller int
                    self.write("[2]uint64{0, uint64(");
                    self.generate_expr(expr);
                    self.write(")}");
                }
                PrimitiveType::Bool => {
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(" != 0)");
                }
                // Endian variants - already handled above
                _ => {
                    self.generate_expr(expr);
                }
            },
            _ => {
                self.generate_expr(expr);
            }
        }
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

    /// Get endianness info from an expression (little_endian, bits)
    fn get_expr_endianness_info(&self, expr: &Expr) -> (bool, u32) {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        if let ExprKind::Cast { ty, .. } = &expr.kind
            && let TypeKind::Primitive(p) = &ty.kind
        {
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
        // Default to little endian, 32 bits
        (true, 32)
    }
}

impl Default for GoGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for GoGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();
        self.needed_imports.clear();
        self.needs_assert = false;
        self.needs_bytes_equal = false;
        self.needs_cond_uint8 = false;
        self.needs_cond_uint16 = false;
        self.needs_cond_uint32 = false;
        self.needs_cond_uint64 = false;
        self.needs_cond_bool = false;
        self.needs_cond_bytes = false;
        self.needs_constant_time_eq = false;

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

        // Pre-scan to determine needed imports and helpers
        self.pre_scan_ast(&ast.ast);

        // Check if we need encoding/binary for the runtime (Reader/Writer)
        // We always include it since Reader/Writer use it
        self.needed_imports.insert("encoding/binary".to_string());

        // Generate into a separate buffer so we know what imports to add
        let mut body_output = String::new();
        std::mem::swap(&mut self.output, &mut body_output);

        self.generate_runtime();

        if self.include_tests {
            // Test helpers will be generated
        }

        // Generate helpers
        self.generate_helpers();

        // Generate all items
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

        // Generate test runner as main() if tests are included
        if self.include_tests && !test_names.is_empty() {
            self.writeln("func main() {");
            self.indent();
            self.writeln("passed := 0");
            self.writeln("failed := 0");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("__test_name = \"{}\"", name));
                self.writeln("__test_failures = 0");
                self.writeln("func() {");
                self.indent();
                self.writeln("defer func() {");
                self.indent();
                self.writeln("if r := recover(); r != nil {");
                self.indent();
                self.writeln(&format!("fmt.Printf(\"FAIL: {} - %v\\n\", r)", name));
                self.writeln("failed++");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("}()");
                self.writeln(&format!("test_{}()", name));
                self.writeln("if __test_failures == 0 {");
                self.indent();
                self.writeln(&format!("fmt.Println(\"PASS: {}\")", name));
                self.writeln("passed++");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("fmt.Println(\"FAIL: {}\")", name));
                self.writeln("failed++");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("}()");
                self.writeln("");
            }

            self.writeln("fmt.Println()");
            self.writeln("fmt.Printf(\"%d passed, %d failed\\n\", passed, failed)");
            self.writeln("if failed > 0 {");
            self.indent();
            self.writeln("panic(\"tests failed\")");
            self.dedent();
            self.writeln("}");
            self.dedent();
            self.writeln("}");
        } else if !self.include_tests {
            // Generate a placeholder main if no tests and no main function exists
            let has_main = ast.ast.items.iter().any(|item| {
                if let ItemKind::Function(f) = &item.kind {
                    f.name.name == "main"
                } else {
                    false
                }
            });
            if !has_main {
                self.writeln("func main() {");
                self.writeln("}");
            }
        }

        // Now build the final output with header
        let generated_body = std::mem::take(&mut self.output);

        // Build the complete file
        self.output = String::new();
        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("");
        self.writeln("package main");
        self.writeln("");

        // Import block
        let mut imports: Vec<String> = self.needed_imports.iter().cloned().collect();
        imports.sort();
        if !imports.is_empty() {
            self.writeln("import (");
            self.indent();
            for imp in &imports {
                self.writeln(&format!("\"{}\"", imp));
            }
            self.dedent();
            self.writeln(")");
            self.writeln("");
        }

        // Suppress unused import warnings
        if self.needed_imports.contains("encoding/binary") {
            self.writeln("var _ = binary.BigEndian");
            self.writeln("");
        }

        self.output.push_str(&generated_body);

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "go"
    }

    fn language_name(&self) -> &'static str {
        "Go"
    }
}

/// Convert a field name to Go-exported style (capitalize first letter)
/// Go structs need exported fields (capitalized) to work properly
fn go_exported_field(name: &str) -> String {
    // Keep the original name to avoid breaking field access patterns
    // In Go, struct fields within the same package don't need to be exported
    name.to_string()
}

/// Escape a string for Go string literals
fn escape_go_string(s: &str) -> String {
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
        ExprKind::Builtin { .. } => false,
        ExprKind::Index { .. } => false,
        ExprKind::Field { .. } => false,
        ExprKind::Ident(_) => false,
        ExprKind::Call { .. } => false,
        _ => false,
    }
}

/// Check if an expression produces a byte sequence (for from_bytes conversion)
fn is_byte_sequence_expr(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Slice { .. } => true,
        ExprKind::Hex(_) | ExprKind::Bytes(_) | ExprKind::String(_) => true,
        ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } => true,
        ExprKind::Index { .. } => false,
        ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Paren(inner) => {
            is_byte_sequence_expr(inner)
        }
        ExprKind::Ident(_) => true,
        ExprKind::Field { .. } => true,
        _ => false,
    }
}

/// Check if an expression produces a byte value (u8)
fn is_byte_value(expr: &Expr) -> bool {
    use crate::parser::{PrimitiveType, TypeKind};

    match &expr.kind {
        ExprKind::Integer(n) => *n <= 255,
        ExprKind::Cast { ty, .. } => {
            if let TypeKind::Primitive(p) = &ty.kind {
                matches!(p.to_native(), PrimitiveType::U8)
            } else {
                false
            }
        }
        ExprKind::Paren(inner) => is_byte_value(inner),
        _ => false,
    }
}
