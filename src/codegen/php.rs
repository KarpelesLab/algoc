//! PHP code generator
//!
//! Generates PHP code from the analyzed AST.
//! Uses integer masking for fixed-width types and arrays for byte buffers.

use super::CodeGenerator;
use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;
use crate::parser::{
    Ast, BinaryOp, Block, BuiltinFunc, Expr, ExprKind, Function, Item, ItemKind, PrimitiveType,
    Stmt, StmtKind, Type as ParserType, UnaryOp,
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

/// PHP code generator
pub struct PhpGenerator {
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
    /// Parameters that need pass-by-reference (&mut)
    mutref_params: HashMap<String, Vec<bool>>,
}

impl PhpGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            mutref_params: HashMap::new(),
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
        self.writeln("// AlgoC Runtime Helpers");
        self.writeln("");

        // Integer masking helpers
        self.writeln("function _u8($x) { return $x & 0xFF; }");
        self.writeln("function _u16($x) { return $x & 0xFFFF; }");
        self.writeln("function _u32($x) { return $x & 0xFFFFFFFF; }");
        self.writeln("function _u64($x) { return $x & 0xFFFFFFFFFFFFFFFF; }");
        self.writeln("");

        // Unsigned right shift helper (PHP >> is arithmetic)
        self.writeln("function _ushr($value, $bits) {");
        self.indent();
        self.writeln("if ($bits === 0) return $value;");
        self.writeln("if ($bits >= 64) return 0;");
        self.writeln("if ($value >= 0) return $value >> $bits;");
        self.writeln("return ($value >> $bits) & (PHP_INT_MAX >> ($bits - 1));");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Unsigned right shift for 32-bit values
        self.writeln("function _ushr32($value, $bits) {");
        self.indent();
        self.writeln("if ($bits === 0) return $value & 0xFFFFFFFF;");
        self.writeln("if ($bits >= 32) return 0;");
        self.writeln("return (_ushr($value, $bits)) & 0xFFFFFFFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Reader class
        self.writeln("class Reader {");
        self.indent();
        self.writeln("public $data;");
        self.writeln("public $pos;");
        self.writeln("");

        self.writeln("public function __construct($data) {");
        self.indent();
        self.writeln("if (is_string($data)) {");
        self.indent();
        self.writeln("$this->data = array_values(unpack('C*', $data));");
        self.dedent();
        self.writeln("} else {");
        self.indent();
        self.writeln("$this->data = $data;");
        self.dedent();
        self.writeln("}");
        self.writeln("$this->pos = 0;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u8
        self.writeln("public function read_u8() {");
        self.indent();
        self.writeln("if ($this->pos >= count($this->data)) throw new \\RuntimeException('EOF');");
        self.writeln("return $this->data[$this->pos++];");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u16be
        self.writeln("public function read_u16() { return $this->read_u16be(); }");
        self.writeln("public function read_u16be() {");
        self.indent();
        self.writeln(
            "if ($this->pos + 2 > count($this->data)) throw new \\RuntimeException('EOF');",
        );
        self.writeln("$v = ($this->data[$this->pos] << 8) | $this->data[$this->pos + 1];");
        self.writeln("$this->pos += 2;");
        self.writeln("return $v;");
        self.dedent();
        self.writeln("}");
        self.writeln("public function read_u16le() {");
        self.indent();
        self.writeln(
            "if ($this->pos + 2 > count($this->data)) throw new \\RuntimeException('EOF');",
        );
        self.writeln("$v = $this->data[$this->pos] | ($this->data[$this->pos + 1] << 8);");
        self.writeln("$this->pos += 2;");
        self.writeln("return $v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u32 variants
        self.writeln("public function read_u32() { return $this->read_u32be(); }");
        self.writeln("public function read_u32be() {");
        self.indent();
        self.writeln(
            "if ($this->pos + 4 > count($this->data)) throw new \\RuntimeException('EOF');",
        );
        self.writeln("$v = ($this->data[$this->pos] << 24) | ($this->data[$this->pos + 1] << 16) | ($this->data[$this->pos + 2] << 8) | $this->data[$this->pos + 3];");
        self.writeln("$this->pos += 4;");
        self.writeln("return $v & 0xFFFFFFFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("public function read_u32le() {");
        self.indent();
        self.writeln(
            "if ($this->pos + 4 > count($this->data)) throw new \\RuntimeException('EOF');",
        );
        self.writeln("$v = $this->data[$this->pos] | ($this->data[$this->pos + 1] << 8) | ($this->data[$this->pos + 2] << 16) | ($this->data[$this->pos + 3] << 24);");
        self.writeln("$this->pos += 4;");
        self.writeln("return $v & 0xFFFFFFFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u64 variants
        self.writeln("public function read_u64() { return $this->read_u64be(); }");
        self.writeln("public function read_u64be() {");
        self.indent();
        self.writeln(
            "if ($this->pos + 8 > count($this->data)) throw new \\RuntimeException('EOF');",
        );
        self.writeln("$hi = $this->read_u32be();");
        self.writeln("$lo = $this->read_u32be();");
        self.writeln("return ($hi << 32) | $lo;");
        self.dedent();
        self.writeln("}");
        self.writeln("public function read_u64le() {");
        self.indent();
        self.writeln(
            "if ($this->pos + 8 > count($this->data)) throw new \\RuntimeException('EOF');",
        );
        self.writeln("$lo = $this->read_u32le();");
        self.writeln("$hi = $this->read_u32le();");
        self.writeln("return ($hi << 32) | $lo;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_bytes
        self.writeln("public function read_bytes($count) {");
        self.indent();
        self.writeln(
            "if ($this->pos + $count > count($this->data)) throw new \\RuntimeException('EOF');",
        );
        self.writeln("$result = array_slice($this->data, $this->pos, $count);");
        self.writeln("$this->pos += $count;");
        self.writeln("return $result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_chunk
        self.writeln("public function read_chunk($max_size) {");
        self.indent();
        self.writeln("$remaining = count($this->data) - $this->pos;");
        self.writeln("$count = min($max_size, $remaining);");
        self.writeln("$result = array_slice($this->data, $this->pos, $count);");
        self.writeln("$this->pos += $count;");
        self.writeln("return $result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // eof
        self.writeln("public function eof() { return $this->pos >= count($this->data); }");

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer class
        self.writeln("class Writer {");
        self.indent();
        self.writeln("public $data;");
        self.writeln("public $pos;");
        self.writeln("");

        self.writeln("public function __construct($data) {");
        self.indent();
        self.writeln("if (is_int($data)) {");
        self.indent();
        self.writeln("$this->data = array_fill(0, $data, 0);");
        self.dedent();
        self.writeln("} else {");
        self.indent();
        self.writeln("$this->data = $data;");
        self.dedent();
        self.writeln("}");
        self.writeln("$this->pos = 0;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u8
        self.writeln("public function write_u8($v) {");
        self.indent();
        self.writeln("if ($this->pos >= count($this->data)) throw new \\RuntimeException('Buffer overflow');");
        self.writeln("$this->data[$this->pos++] = $v & 0xFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u16
        self.writeln("public function write_u16($v) { $this->write_u16be($v); }");
        self.writeln("public function write_u16be($v) {");
        self.indent();
        self.writeln("if ($this->pos + 2 > count($this->data)) throw new \\RuntimeException('Buffer overflow');");
        self.writeln("$this->data[$this->pos++] = ($v >> 8) & 0xFF;");
        self.writeln("$this->data[$this->pos++] = $v & 0xFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("public function write_u16le($v) {");
        self.indent();
        self.writeln("if ($this->pos + 2 > count($this->data)) throw new \\RuntimeException('Buffer overflow');");
        self.writeln("$this->data[$this->pos++] = $v & 0xFF;");
        self.writeln("$this->data[$this->pos++] = ($v >> 8) & 0xFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u32
        self.writeln("public function write_u32($v) { $this->write_u32be($v); }");
        self.writeln("public function write_u32be($v) {");
        self.indent();
        self.writeln("if ($this->pos + 4 > count($this->data)) throw new \\RuntimeException('Buffer overflow');");
        self.writeln("$this->data[$this->pos++] = _ushr($v, 24) & 0xFF;");
        self.writeln("$this->data[$this->pos++] = _ushr($v, 16) & 0xFF;");
        self.writeln("$this->data[$this->pos++] = _ushr($v, 8) & 0xFF;");
        self.writeln("$this->data[$this->pos++] = $v & 0xFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("public function write_u32le($v) {");
        self.indent();
        self.writeln("if ($this->pos + 4 > count($this->data)) throw new \\RuntimeException('Buffer overflow');");
        self.writeln("$this->data[$this->pos++] = $v & 0xFF;");
        self.writeln("$this->data[$this->pos++] = _ushr($v, 8) & 0xFF;");
        self.writeln("$this->data[$this->pos++] = _ushr($v, 16) & 0xFF;");
        self.writeln("$this->data[$this->pos++] = _ushr($v, 24) & 0xFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u64
        self.writeln("public function write_u64($v) { $this->write_u64be($v); }");
        self.writeln("public function write_u64be($v) {");
        self.indent();
        self.writeln("if ($this->pos + 8 > count($this->data)) throw new \\RuntimeException('Buffer overflow');");
        self.writeln("$this->write_u32be(_ushr($v, 32) & 0xFFFFFFFF);");
        self.writeln("$this->write_u32be($v & 0xFFFFFFFF);");
        self.dedent();
        self.writeln("}");
        self.writeln("public function write_u64le($v) {");
        self.indent();
        self.writeln("if ($this->pos + 8 > count($this->data)) throw new \\RuntimeException('Buffer overflow');");
        self.writeln("$this->write_u32le($v & 0xFFFFFFFF);");
        self.writeln("$this->write_u32le(_ushr($v, 32) & 0xFFFFFFFF);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_bytes
        self.writeln("public function write_bytes($data) {");
        self.indent();
        self.writeln("if ($this->pos + count($data) > count($this->data)) throw new \\RuntimeException('Buffer overflow');");
        self.writeln("for ($i = 0; $i < count($data); $i++) {");
        self.indent();
        self.writeln("$this->data[$this->pos++] = $data[$i];");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Bytes from int helpers
        self.writeln("function _int_to_bytes_be($value, $len) {");
        self.indent();
        self.writeln("$result = array_fill(0, $len, 0);");
        self.writeln("for ($i = $len - 1; $i >= 0; $i--) {");
        self.indent();
        self.writeln("$result[$i] = $value & 0xFF;");
        self.writeln("$value = _ushr($value, 8);");
        self.dedent();
        self.writeln("}");
        self.writeln("return $result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("function _int_to_bytes_le($value, $len) {");
        self.indent();
        self.writeln("$result = array_fill(0, $len, 0);");
        self.writeln("for ($i = 0; $i < $len; $i++) {");
        self.indent();
        self.writeln("$result[$i] = $value & 0xFF;");
        self.writeln("$value = _ushr($value, 8);");
        self.dedent();
        self.writeln("}");
        self.writeln("return $result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Bytes to int helpers
        self.writeln("function _bytes_to_int_be($bytes) {");
        self.indent();
        self.writeln("$result = 0;");
        self.writeln("for ($i = 0; $i < count($bytes); $i++) {");
        self.indent();
        self.writeln("$result = ($result << 8) | ($bytes[$i] & 0xFF);");
        self.dedent();
        self.writeln("}");
        self.writeln("return $result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("function _bytes_to_int_le($bytes) {");
        self.indent();
        self.writeln("$result = 0;");
        self.writeln("$len = count($bytes);");
        self.writeln("for ($i = $len - 1; $i >= 0; $i--) {");
        self.indent();
        self.writeln("$result = ($result << 8) | ($bytes[$i] & 0xFF);");
        self.dedent();
        self.writeln("}");
        self.writeln("return $result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Endian write to slice
        self.writeln("function _write_endian_to_slice(&$arr, $offset, $value, $byte_count, $little_endian) {");
        self.indent();
        self.writeln("if ($little_endian) {");
        self.indent();
        self.writeln("for ($i = 0; $i < $byte_count; $i++) {");
        self.indent();
        self.writeln("$arr[$offset + $i] = _ushr($value, $i * 8) & 0xFF;");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("} else {");
        self.indent();
        self.writeln("for ($i = 0; $i < $byte_count; $i++) {");
        self.indent();
        self.writeln("$arr[$offset + $i] = _ushr($value, ($byte_count - 1 - $i) * 8) & 0xFF;");
        self.dedent();
        self.writeln("}");
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

        self.writeln("$__test_failures = 0;");
        self.writeln("$__test_name = '';");
        self.writeln("");

        self.writeln("function __assert($condition) {");
        self.indent();
        self.writeln("global $__test_failures, $__test_name;");
        self.writeln("if (!$condition) {");
        self.indent();
        self.writeln("$__test_failures++;");
        self.writeln("echo '  ASSERTION FAILED in ' . $__test_name . \"\\n\";");
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

    fn generate_method(&mut self, struct_name: &str, func: &Function) {
        let mangled_name = format!("{}__{}", struct_name, func.name.name);

        // Build parameter list - first param is &self or &mut self
        let mut params = Vec::new();
        let mut is_mutref = Vec::new();
        for param in &func.params {
            let is_mut = matches!(param.ty.kind, crate::parser::TypeKind::MutRef(_));
            if is_mut {
                params.push(format!("&${}", param.name.name));
            } else {
                params.push(format!("${}", param.name.name));
            }
            is_mutref.push(is_mut);
        }
        self.mutref_params.insert(mangled_name.clone(), is_mutref);

        self.writeln(&format!(
            "function {}({}) {{",
            mangled_name,
            params.join(", ")
        ));
        self.indent();
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("function test_{}() {{", test.name.name));
        self.indent();
        self.writeln("global $__test_failures, $__test_name;");
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        // Check if value is an array — PHP const supports arrays
        let is_array = matches!(
            c.value.kind,
            ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } | ExprKind::Hex(_)
        );
        if is_array {
            // Use define() or a global for array constants — or use const with array literal
            self.write_indent();
            self.write(&format!("const {} = ", c.name.name));
            self.generate_expr(&c.value);
            self.write(";\n\n");
        } else {
            self.write_indent();
            self.write(&format!("const {} = ", c.name.name));
            self.generate_expr(&c.value);
            self.write(";\n\n");
        }
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Generate a factory function for the struct
        self.writeln(&format!("function create_{}() {{", s.name.name));
        self.indent();
        self.writeln("return [");
        self.indent();
        for field in &s.fields {
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("'{}' => {},", field.name.name, init));
        }
        self.dedent();
        self.writeln("];");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs
        self.writeln(&format!("function create_{}() {{", l.name.name));
        self.indent();
        self.writeln("return [");
        self.indent();
        for field in &l.fields {
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("'{}' => {},", field.name.name, init));
        }
        self.dedent();
        self.writeln("];");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum variants as factory functions
        // Each variant returns an associative array with 'tag' key
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!(
                        "function {}__{}() {{ return ['tag' => '{}']; }}",
                        e.name.name, variant.name.name, variant.name.name
                    ));
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    let params: Vec<String> =
                        (0..types.len()).map(|i| format!("$v{}", i)).collect();
                    let fields: Vec<String> = (0..types.len())
                        .map(|i| format!("'v{}' => $v{}", i, i))
                        .collect();
                    self.writeln(&format!(
                        "function {}__{}({}) {{ return ['tag' => '{}', {}]; }}",
                        e.name.name,
                        variant.name.name,
                        params.join(", "),
                        variant.name.name,
                        fields.join(", ")
                    ));
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    let params: Vec<String> =
                        fields.iter().map(|f| format!("${}", f.name.name)).collect();
                    let field_entries: Vec<String> = fields
                        .iter()
                        .map(|f| format!("'{}' => ${}", f.name.name, f.name.name))
                        .collect();
                    self.writeln(&format!(
                        "function {}__{}({}) {{ return ['tag' => '{}', {}]; }}",
                        e.name.name,
                        variant.name.name,
                        params.join(", "),
                        variant.name.name,
                        field_entries.join(", ")
                    ));
                }
            }
        }
        self.writeln("");
    }

    fn default_value_for_type(&self, ty: &ParserType) -> String {
        match &ty.kind {
            crate::parser::TypeKind::Primitive(_) => "0".to_string(),
            crate::parser::TypeKind::Array { element: _, size } => {
                format!("array_fill(0, {}, 0)", size)
            }
            crate::parser::TypeKind::Named(ident) => {
                format!("create_{}()", ident.name)
            }
            _ => "null".to_string(),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        // Track which parameters need pass-by-reference
        let mut params = Vec::new();
        let mut is_mutref = Vec::new();
        for param in &func.params {
            let is_mut = matches!(param.ty.kind, crate::parser::TypeKind::MutRef(_));
            if is_mut {
                params.push(format!("&${}", param.name.name));
            } else {
                params.push(format!("${}", param.name.name));
            }
            is_mutref.push(is_mut);
        }
        self.mutref_params.insert(func.name.name.clone(), is_mutref);

        self.write_indent();
        self.write(&format!("function {}(", func.name.name));
        self.write(&params.join(", "));
        self.write(") {\n");
        self.indent();

        // Track struct types for parameters
        for param in &func.params {
            if let crate::parser::TypeKind::Named(type_ident) = &param.ty.kind {
                self.var_types
                    .insert(param.name.name.clone(), type_ident.name.clone());
            }
            if let crate::parser::TypeKind::MutRef(inner) = &param.ty.kind
                && let crate::parser::TypeKind::Named(type_ident) = &inner.kind
            {
                self.var_types
                    .insert(param.name.name.clone(), type_ident.name.clone());
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
                    // Also handle TypeStaticCall for H::new() style calls
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
                self.write(&format!("${} = ", name.name));
                if let Some(init) = init {
                    self.generate_expr(init);
                } else if let Some(ty) = ty {
                    self.write(&self.default_value_for_type(ty));
                } else {
                    self.write("null");
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
                    && p.endianness() != crate::parser::Endianness::Native
                    && let ExprKind::Slice { array, start, .. } = &inner.kind
                {
                    let little_endian = p.endianness() == crate::parser::Endianness::Little;
                    let byte_count = match p.to_native() {
                        PrimitiveType::U16 | PrimitiveType::I16 => 2,
                        PrimitiveType::U32 | PrimitiveType::I32 => 4,
                        PrimitiveType::U64 | PrimitiveType::I64 => 8,
                        _ => 4,
                    };
                    self.write_indent();
                    self.write("_write_endian_to_slice(");
                    // Pass array by reference
                    self.write("$");
                    // Get the variable name from the array expression
                    if let ExprKind::Ident(ident) = &array.kind {
                        self.write(&ident.name);
                    } else {
                        // For more complex expressions, generate a temporary
                        self.write("__tmp");
                    }
                    self.write(", ");
                    self.generate_expr(start);
                    self.write(", ");
                    self.generate_expr(value);
                    self.write(&format!(", {}, {});\n", byte_count, little_endian));
                    return;
                }

                self.write_indent();
                self.generate_assign_target(target);
                self.write(" = ");
                self.generate_expr(value);
                self.write(";\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                self.write_indent();
                // PHP's >> is arithmetic, so Shr needs special handling
                if matches!(op, BinaryOp::Shr) {
                    // target = _ushr32(target, value)
                    self.generate_assign_target(target);
                    self.write(" = _ushr32(");
                    self.generate_expr(target);
                    self.write(", ");
                    self.generate_expr(value);
                    self.write(");\n");
                } else {
                    self.generate_assign_target(target);
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
                        BinaryOp::Shr => ">>=", // Won't reach here
                        _ => "=",
                    };
                    self.write(&format!(" {} ", op_str));
                    self.generate_expr(value);
                    self.write(";\n");
                }
            }
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
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
            StmtKind::For {
                var,
                start,
                end,
                inclusive,
                body,
            } => {
                self.write_indent();
                self.write(&format!("for (${} = ", var.name));
                self.generate_expr(start);
                self.write(&format!(
                    "; ${} {} ",
                    var.name,
                    if *inclusive { "<=" } else { "<" }
                ));
                self.generate_expr(end);
                self.write(&format!("; ${}++) {{\n", var.name));
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

    /// Generate assignment target (lvalue) - handles PHP $ prefix and field access
    fn generate_assign_target(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Ident(ident) => {
                self.write(&format!("${}", ident.name));
            }
            ExprKind::Index { array, index } => {
                self.generate_assign_target(array);
                self.write("[");
                self.generate_expr(index);
                self.write("]");
            }
            ExprKind::Field { object, field } => {
                self.generate_assign_target(object);
                self.write(&format!("['{}']", field.name));
            }
            ExprKind::Deref(inner) => {
                self.generate_assign_target(inner);
            }
            _ => {
                // Fallback: generate as expression
                self.generate_expr(expr);
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
                // Convert string to byte array
                self.write(&format!(
                    "array_values(unpack('C*', \"{}\"))",
                    escape_php_string(s)
                ));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!(
                    "array_values(unpack('C*', \"{}\"))",
                    escape_php_string(s)
                ));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to array of bytes
                if h.is_empty() {
                    self.write("[]");
                } else {
                    self.write("array_values(unpack('C*', hex2bin('");
                    self.write(h);
                    self.write("')))");
                }
            }
            ExprKind::Ident(ident) => {
                self.write(&format!("${}", ident.name));
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

                // Handle PHP-specific right shift (arithmetic)
                if matches!(op, BinaryOp::Shr) {
                    self.write("_ushr32(");
                    self.generate_expr(left);
                    self.write(", ");
                    self.generate_expr(right);
                    self.write(")");
                    return;
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
                    BinaryOp::Shr => " >> ", // Won't reach here due to early return
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
                self.generate_expr(right);
                self.write(")");
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
            }
            ExprKind::Index { array, index } => {
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(index);
                self.write("]");
            }
            ExprKind::Slice {
                array, start, end, ..
            } => {
                self.write("array_slice(");
                self.generate_expr(array);
                self.write(", ");
                self.generate_expr(start);
                self.write(", ");
                // array_slice takes length, not end index
                self.write("(");
                self.generate_expr(end);
                self.write(") - (");
                self.generate_expr(start);
                self.write("))");
            }
            ExprKind::Field { object, field } => {
                self.generate_expr(object);
                self.write(&format!("['{}']", field.name));
            }
            ExprKind::Call { func, args } => {
                // Check for Reader/Writer constructor calls
                if let ExprKind::Ident(ident) = &func.kind
                    && (ident.name == "Reader" || ident.name == "Writer")
                {
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

                // Check for method calls like slice.len() or reader.read_u32()
                if let ExprKind::Field { object, field } = &func.kind {
                    if field.name == "len" && args.is_empty() {
                        // Convert .len() to count()
                        self.write("count(");
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
                        self.write("(function() use (&$");
                        self.write(&var_ident.name);
                        self.write(", $");
                        // Get reader var name
                        if let ExprKind::Ident(reader_ident) = &object.kind {
                            self.write(&reader_ident.name);
                        }
                        self.write(") { ");
                        for field_info in &fields {
                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty)
                            {
                                self.write(&format!(
                                    "${}['{}'] = $",
                                    var_ident.name, field_info.name
                                ));
                                if let ExprKind::Ident(reader_ident) = &object.kind {
                                    self.write(&reader_ident.name);
                                }
                                self.write(&format!("->{}(); ", read_method));
                            }
                        }
                        self.write("})()");
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
                            self.write("(function() use ($");
                            self.write(&var_ident.name);
                            self.write(", $");
                            if let ExprKind::Ident(writer_ident) = &object.kind {
                                self.write(&writer_ident.name);
                            }
                            self.write(") { ");
                            for field_info in &fields {
                                if let Some(write_method) =
                                    self.get_write_method_for_type(&field_info.ty)
                                {
                                    self.write("$");
                                    if let ExprKind::Ident(writer_ident) = &object.kind {
                                        self.write(&writer_ident.name);
                                    }
                                    self.write(&format!(
                                        "->{}(${}['{}']); ",
                                        write_method, var_ident.name, field_info.name
                                    ));
                                }
                            }
                            self.write("})()");
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
                        self.write(&format!("->{}(", field.name));
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_expr(arg);
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
                        // Generate: StructName__method($object, $args...)
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
                self.write("array_fill(0, ");
                self.generate_expr(count);
                self.write(", ");
                self.generate_expr(value);
                self.write(")");
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in PHP are handled at the function parameter level
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are no-ops in PHP
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
                self.write("[");
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("'{}' => ", field_name.name));
                    self.generate_expr(value);
                }
                self.write("]");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // PHP ternary: condition ? then : else
                self.write("(");
                self.generate_expr(condition);
                self.write(" ? ");
                self.generate_expr(then_expr);
                self.write(" : ");
                self.generate_expr(else_expr);
                self.write(")");
            }
            ExprKind::EnumVariant {
                enum_name,
                variant_name,
                args,
            } => {
                // Generate: EnumName__VariantName() or EnumName__VariantName(args...)
                if args.is_empty() {
                    self.write(&format!("{}__{}()", enum_name.name, variant_name.name));
                } else {
                    self.write(&format!("{}__{}(", enum_name.name, variant_name.name));
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
                self.write("(function($__match) { ");
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write(" else");
                    }
                    self.generate_pattern_match(&arm.pattern, "$__match");
                    self.write(" { return ");
                    self.generate_expr(&arm.body);
                    self.write("; }");
                }
                self.write(" })(");
                self.generate_expr(expr);
                self.write(")");
            }
            ExprKind::MethodCall {
                receiver,
                mangled_name,
                args,
                ..
            } => {
                // Generate: mangled_name($receiver, $args...)
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
                // Should be resolved by monomorphization - generate placeholder
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
                self.write(" if (true)");
            }
            PatternKind::Literal(lit_expr) => {
                self.write(&format!(" if ({} === ", scrutinee));
                self.generate_expr(lit_expr);
                self.write(")");
            }
            PatternKind::Ident(ident) => {
                // Binding pattern - always matches, bind the value
                self.write(&format!(
                    " if ((function() {{ ${} = {}; return true; }})())",
                    ident.name, scrutinee
                ));
            }
            PatternKind::EnumVariant {
                enum_name: _,
                variant_name,
                bindings,
            } => {
                self.write(&format!(
                    " if ({}['tag'] === '{}'",
                    scrutinee, variant_name.name
                ));
                if !bindings.is_empty() {
                    // Bindings are handled in the body
                }
                self.write(")");
            }
            PatternKind::Tuple(_patterns) => {
                self.write(" if (true)"); // Simplified
            }
            PatternKind::Or(patterns) => {
                self.write(" if (");
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" || ");
                    }
                    self.write("(");
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
                self.write(&format!("{}['tag'] === '{}'", scrutinee, variant_name.name));
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
        use crate::parser::{Endianness, TypeKind};

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
        use crate::parser::{Endianness, TypeKind};

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
        use crate::parser::{Endianness, TypeKind};

        // Check for endian byte conversions (byte slice/array to integer)
        if let TypeKind::Primitive(p) = &ty.kind {
            let endian = p.endianness();
            if endian != Endianness::Native {
                let is_little = endian == Endianness::Little;

                // Check if source is a slice/array (byte conversion)
                if is_byte_sequence_expr(expr) {
                    if is_little {
                        self.write("_bytes_to_int_le(");
                    } else {
                        self.write("_bytes_to_int_be(");
                    }
                    self.generate_expr(expr);
                    self.write(")");
                    return;
                }

                // Integer to integer with different endianness - just mask
                let native = p.to_native();
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => {
                        self.write("_u8(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        self.write("_u16(");
                        self.generate_expr(expr);
                        self.write(")");
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
                        // 128-bit not natively supported, mask as best we can
                        self.write("(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    _ => {
                        self.generate_expr(expr);
                    }
                }
                return;
            }
        }

        // Check for integer to byte array cast
        // e.g., value as u8[4] -> _int_to_bytes_be/le(value, 4)
        if let TypeKind::Array { element, size } = &ty.kind
            && let TypeKind::Primitive(PrimitiveType::U8) = &element.kind
        {
            let (is_little, _bits) = self.get_expr_endianness_info(expr);
            if is_little {
                self.write("_int_to_bytes_le(");
            } else {
                self.write("_int_to_bytes_be(");
            }
            self.generate_expr(expr);
            self.write(&format!(", {})", size));
            return;
        }

        // Standard casts - masking to appropriate bit widths
        match &ty.kind {
            TypeKind::Primitive(p) => match p {
                PrimitiveType::U8 | PrimitiveType::I8 => {
                    self.write("_u8(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::U16 | PrimitiveType::I16 => {
                    self.write("_u16(");
                    self.generate_expr(expr);
                    self.write(")");
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
                    // PHP doesn't have native 128-bit ints; pass through for now
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::Bool => {
                    self.write("(bool)(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                // Endian types that reach here (shouldn't normally, but fallback)
                _ => {
                    self.generate_expr(expr);
                }
            },
            _ => {
                self.generate_expr(expr);
            }
        }
    }

    /// Get endianness info from an expression (little_endian, bits)
    fn get_expr_endianness_info(&self, expr: &Expr) -> (bool, u32) {
        use crate::parser::{Endianness, TypeKind};

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
        ExprKind::Index { .. } => false, // Single element
        ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Paren(inner) => {
            is_byte_sequence_expr(inner)
        }
        ExprKind::Ident(_) => true, // Assume variables can be byte sequences
        ExprKind::Field { .. } => true,
        _ => false,
    }
}

impl Default for PhpGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for PhpGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();
        self.mutref_params.clear();

        // Pre-pass: collect struct field info and methods for read/write generation
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

        self.writeln("<?php");
        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
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

        // Generate test runner if tests are included
        if self.include_tests {
            self.writeln("// Test Runner");
            self.writeln("function run_tests() {");
            self.indent();
            self.writeln("global $__test_failures, $__test_name;");
            self.writeln("$__passed = 0;");
            self.writeln("$__failed = 0;");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("$__test_name = '{}';", name));
                self.writeln("$__test_failures = 0;");
                self.writeln("try {");
                self.indent();
                self.writeln(&format!("test_{}();", name));
                self.writeln("if ($__test_failures === 0) {");
                self.indent();
                self.writeln(&format!("echo \"PASS: {}\\n\";", name));
                self.writeln("$__passed++;");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("echo \"FAIL: {}\\n\";", name));
                self.writeln("$__failed++;");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("} catch (\\Exception $e) {");
                self.indent();
                self.writeln(&format!(
                    "echo \"FAIL: {} - \" . $e->getMessage() . \"\\n\";",
                    name
                ));
                self.writeln("$__failed++;");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("echo \"\\n\";");
            self.writeln("echo $__passed . ' passed, ' . $__failed . \" failed\\n\";");
            self.writeln("return $__failed === 0;");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // Auto-run tests if tests are included
        if self.include_tests {
            self.writeln("// Auto-run tests");
            self.writeln("exit(run_tests() ? 0 : 1);");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "php"
    }

    fn language_name(&self) -> &'static str {
        "PHP"
    }
}

fn escape_php_string(s: &str) -> String {
    let mut result = String::new();
    for c in s.chars() {
        match c {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '$' => result.push_str("\\$"),
            _ => result.push(c),
        }
    }
    result
}
