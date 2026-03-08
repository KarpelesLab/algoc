//! C++ code generator
//!
//! Generates C++20 code from the analyzed AST.
//! Uses std::vector<uint8_t> for byte buffers, std::span for slices,
//! and fixed-width integer types from <cstdint>.

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

/// C++ code generator
pub struct CppGenerator {
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

impl CppGenerator {
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
            self.output.push_str("  ");
        }
    }

    fn indent(&mut self) {
        self.indent += 1;
    }

    fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    /// Generate the #include directives and helper functions
    fn generate_runtime(&mut self) {
        self.writeln("#include <cstdint>");
        self.writeln("#include <cstring>");
        self.writeln("#include <vector>");
        self.writeln("#include <array>");
        self.writeln("#include <span>");
        self.writeln("#include <iostream>");
        self.writeln("#include <string>");
        self.writeln("#include <functional>");
        self.writeln("#include <algorithm>");
        self.writeln("#include <stdexcept>");
        self.writeln("#include <cassert>");
        self.writeln("");

        // Byte conversion / endian helpers
        self.writeln("// AlgoC Runtime Helpers");
        self.writeln("");

        // Helper to create vector from initializer list
        self.writeln("static std::vector<uint8_t> make_bytes(std::initializer_list<uint8_t> il) {");
        self.indent();
        self.writeln("return std::vector<uint8_t>(il);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Endian read helpers
        self.writeln("static uint16_t read_u16be(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint16_t(p[0]) << 8) | uint16_t(p[1]);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint16_t read_u16le(const uint8_t* p) {");
        self.indent();
        self.writeln("return uint16_t(p[0]) | (uint16_t(p[1]) << 8);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint32_t read_u32be(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16) | (uint32_t(p[2]) << 8) | uint32_t(p[3]);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint32_t read_u32le(const uint8_t* p) {");
        self.indent();
        self.writeln("return uint32_t(p[0]) | (uint32_t(p[1]) << 8) | (uint32_t(p[2]) << 16) | (uint32_t(p[3]) << 24);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint64_t read_u64be(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint64_t(p[0]) << 56) | (uint64_t(p[1]) << 48) | (uint64_t(p[2]) << 40) | (uint64_t(p[3]) << 32) | (uint64_t(p[4]) << 24) | (uint64_t(p[5]) << 16) | (uint64_t(p[6]) << 8) | uint64_t(p[7]);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint64_t read_u64le(const uint8_t* p) {");
        self.indent();
        self.writeln("return uint64_t(p[0]) | (uint64_t(p[1]) << 8) | (uint64_t(p[2]) << 16) | (uint64_t(p[3]) << 24) | (uint64_t(p[4]) << 32) | (uint64_t(p[5]) << 40) | (uint64_t(p[6]) << 48) | (uint64_t(p[7]) << 56);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // __uint128_t read helpers
        self.writeln("static __uint128_t read_u128be(const uint8_t* p) {");
        self.indent();
        self.writeln("return (__uint128_t(read_u64be(p)) << 64) | __uint128_t(read_u64be(p + 8));");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static __uint128_t read_u128le(const uint8_t* p) {");
        self.indent();
        self.writeln("return __uint128_t(read_u64le(p)) | (__uint128_t(read_u64le(p + 8)) << 64);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Endian write helpers
        self.writeln("static void write_u16be(uint8_t* p, uint16_t v) {");
        self.indent();
        self.writeln("p[0] = uint8_t(v >> 8); p[1] = uint8_t(v);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void write_u16le(uint8_t* p, uint16_t v) {");
        self.indent();
        self.writeln("p[0] = uint8_t(v); p[1] = uint8_t(v >> 8);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void write_u32be(uint8_t* p, uint32_t v) {");
        self.indent();
        self.writeln("p[0] = uint8_t(v >> 24); p[1] = uint8_t(v >> 16); p[2] = uint8_t(v >> 8); p[3] = uint8_t(v);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void write_u32le(uint8_t* p, uint32_t v) {");
        self.indent();
        self.writeln("p[0] = uint8_t(v); p[1] = uint8_t(v >> 8); p[2] = uint8_t(v >> 16); p[3] = uint8_t(v >> 24);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void write_u64be(uint8_t* p, uint64_t v) {");
        self.indent();
        self.writeln("p[0] = uint8_t(v >> 56); p[1] = uint8_t(v >> 48); p[2] = uint8_t(v >> 40); p[3] = uint8_t(v >> 32); p[4] = uint8_t(v >> 24); p[5] = uint8_t(v >> 16); p[6] = uint8_t(v >> 8); p[7] = uint8_t(v);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void write_u64le(uint8_t* p, uint64_t v) {");
        self.indent();
        self.writeln("p[0] = uint8_t(v); p[1] = uint8_t(v >> 8); p[2] = uint8_t(v >> 16); p[3] = uint8_t(v >> 24); p[4] = uint8_t(v >> 32); p[5] = uint8_t(v >> 40); p[6] = uint8_t(v >> 48); p[7] = uint8_t(v >> 56);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void write_u128be(uint8_t* p, __uint128_t v) {");
        self.indent();
        self.writeln("write_u64be(p, uint64_t(v >> 64)); write_u64be(p + 8, uint64_t(v));");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void write_u128le(uint8_t* p, __uint128_t v) {");
        self.indent();
        self.writeln("write_u64le(p, uint64_t(v)); write_u64le(p + 8, uint64_t(v >> 64));");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Reader class
        self.writeln("struct Reader {");
        self.indent();
        self.writeln("const uint8_t* data;");
        self.writeln("size_t len;");
        self.writeln("size_t pos;");
        self.writeln("");
        self.writeln(
            "Reader(std::span<const uint8_t> s) : data(s.data()), len(s.size()), pos(0) {}",
        );
        self.writeln(
            "Reader(const std::vector<uint8_t>& v) : data(v.data()), len(v.size()), pos(0) {}",
        );
        self.writeln("");
        self.writeln("uint8_t read_u8() {");
        self.indent();
        self.writeln("if (pos >= len) throw std::runtime_error(\"EOF\");");
        self.writeln("return data[pos++];");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("uint16_t read_u16() { return read_u16be(); }");
        self.writeln("uint16_t read_u16be() {");
        self.indent();
        self.writeln("if (pos + 2 > len) throw std::runtime_error(\"EOF\");");
        self.writeln("uint16_t v = ::read_u16be(data + pos); pos += 2; return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("uint16_t read_u16le() {");
        self.indent();
        self.writeln("if (pos + 2 > len) throw std::runtime_error(\"EOF\");");
        self.writeln("uint16_t v = ::read_u16le(data + pos); pos += 2; return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("uint32_t read_u32() { return read_u32be(); }");
        self.writeln("uint32_t read_u32be() {");
        self.indent();
        self.writeln("if (pos + 4 > len) throw std::runtime_error(\"EOF\");");
        self.writeln("uint32_t v = ::read_u32be(data + pos); pos += 4; return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("uint32_t read_u32le() {");
        self.indent();
        self.writeln("if (pos + 4 > len) throw std::runtime_error(\"EOF\");");
        self.writeln("uint32_t v = ::read_u32le(data + pos); pos += 4; return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("uint64_t read_u64() { return read_u64be(); }");
        self.writeln("uint64_t read_u64be() {");
        self.indent();
        self.writeln("if (pos + 8 > len) throw std::runtime_error(\"EOF\");");
        self.writeln("uint64_t v = ::read_u64be(data + pos); pos += 8; return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("uint64_t read_u64le() {");
        self.indent();
        self.writeln("if (pos + 8 > len) throw std::runtime_error(\"EOF\");");
        self.writeln("uint64_t v = ::read_u64le(data + pos); pos += 8; return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("std::vector<uint8_t> read_bytes(size_t count) {");
        self.indent();
        self.writeln("if (pos + count > len) throw std::runtime_error(\"EOF\");");
        self.writeln("std::vector<uint8_t> result(data + pos, data + pos + count);");
        self.writeln("pos += count;");
        self.writeln("return result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("std::vector<uint8_t> read_chunk(size_t max_size) {");
        self.indent();
        self.writeln("size_t remaining = len - pos;");
        self.writeln("size_t count = std::min(max_size, remaining);");
        self.writeln("std::vector<uint8_t> result(data + pos, data + pos + count);");
        self.writeln("pos += count;");
        self.writeln("return result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("bool eof() const { return pos >= len; }");
        self.dedent();
        self.writeln("};");
        self.writeln("");

        // Writer class
        self.writeln("struct Writer {");
        self.indent();
        self.writeln("uint8_t* data;");
        self.writeln("size_t len;");
        self.writeln("size_t pos;");
        self.writeln("");
        self.writeln("Writer(std::span<uint8_t> s) : data(s.data()), len(s.size()), pos(0) {}");
        self.writeln("Writer(std::vector<uint8_t>& v) : data(v.data()), len(v.size()), pos(0) {}");
        self.writeln("");
        self.writeln("void write_u8(uint8_t v) {");
        self.indent();
        self.writeln("if (pos >= len) throw std::runtime_error(\"Buffer overflow\");");
        self.writeln("data[pos++] = v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("void write_u16(uint16_t v) { write_u16be(v); }");
        self.writeln("void write_u16be(uint16_t v) {");
        self.indent();
        self.writeln("if (pos + 2 > len) throw std::runtime_error(\"Buffer overflow\");");
        self.writeln("::write_u16be(data + pos, v); pos += 2;");
        self.dedent();
        self.writeln("}");
        self.writeln("void write_u16le(uint16_t v) {");
        self.indent();
        self.writeln("if (pos + 2 > len) throw std::runtime_error(\"Buffer overflow\");");
        self.writeln("::write_u16le(data + pos, v); pos += 2;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("void write_u32(uint32_t v) { write_u32be(v); }");
        self.writeln("void write_u32be(uint32_t v) {");
        self.indent();
        self.writeln("if (pos + 4 > len) throw std::runtime_error(\"Buffer overflow\");");
        self.writeln("::write_u32be(data + pos, v); pos += 4;");
        self.dedent();
        self.writeln("}");
        self.writeln("void write_u32le(uint32_t v) {");
        self.indent();
        self.writeln("if (pos + 4 > len) throw std::runtime_error(\"Buffer overflow\");");
        self.writeln("::write_u32le(data + pos, v); pos += 4;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("void write_u64(uint64_t v) { write_u64be(v); }");
        self.writeln("void write_u64be(uint64_t v) {");
        self.indent();
        self.writeln("if (pos + 8 > len) throw std::runtime_error(\"Buffer overflow\");");
        self.writeln("::write_u64be(data + pos, v); pos += 8;");
        self.dedent();
        self.writeln("}");
        self.writeln("void write_u64le(uint64_t v) {");
        self.indent();
        self.writeln("if (pos + 8 > len) throw std::runtime_error(\"Buffer overflow\");");
        self.writeln("::write_u64le(data + pos, v); pos += 8;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.writeln("void write_bytes(std::span<const uint8_t> d) {");
        self.indent();
        self.writeln("if (pos + d.size() > len) throw std::runtime_error(\"Buffer overflow\");");
        self.writeln("std::memcpy(data + pos, d.data(), d.size());");
        self.writeln("pos += d.size();");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("};");
        self.writeln("");

        // Slice helper: returns a std::vector<uint8_t> from a subrange
        self.writeln("static std::vector<uint8_t> slice_vec(std::span<const uint8_t> s, size_t start, size_t end) {");
        self.indent();
        self.writeln("return std::vector<uint8_t>(s.begin() + start, s.begin() + end);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static std::vector<uint8_t> slice_vec(const std::vector<uint8_t>& v, size_t start, size_t end) {");
        self.indent();
        self.writeln("return std::vector<uint8_t>(v.begin() + start, v.begin() + end);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Copy from span to vector range
        self.writeln("static void copy_to_slice(std::vector<uint8_t>& dst, size_t start, size_t end, std::span<const uint8_t> src) {");
        self.indent();
        self.writeln("std::memcpy(dst.data() + start, src.data(), end - start);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // hex string to vector
        self.writeln("static std::vector<uint8_t> hex_to_bytes(const char* hex) {");
        self.indent();
        self.writeln("std::vector<uint8_t> result;");
        self.writeln("while (*hex) {");
        self.indent();
        self.writeln("uint8_t hi = (*hex >= 'a') ? (*hex - 'a' + 10) : ((*hex >= 'A') ? (*hex - 'A' + 10) : (*hex - '0'));");
        self.writeln("hex++;");
        self.writeln("uint8_t lo = (*hex >= 'a') ? (*hex - 'a' + 10) : ((*hex >= 'A') ? (*hex - 'A' + 10) : (*hex - '0'));");
        self.writeln("hex++;");
        self.writeln("result.push_back((hi << 4) | lo);");
        self.dedent();
        self.writeln("}");
        self.writeln("return result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // string to bytes
        self.writeln("static std::vector<uint8_t> string_to_bytes(const char* s, size_t len) {");
        self.indent();
        self.writeln("return std::vector<uint8_t>(s, s + len);");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Generate test runtime helpers (only when include_tests is true)
    fn generate_test_runtime(&mut self) {
        self.writeln("// Test Helpers");
        self.writeln("");
        self.writeln("static int __test_failures = 0;");
        self.writeln("static std::string __test_name;");
        self.writeln("");

        self.writeln("static void __assert(bool condition) {");
        self.indent();
        self.writeln("if (!condition) {");
        self.indent();
        self.writeln("__test_failures++;");
        self.writeln("std::cout << \"  ASSERTION FAILED in \" << __test_name << std::endl;");
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

        // Build return type
        let ret_type = if let Some(ret_ty) = &func.return_type {
            self.type_to_cpp(ret_ty)
        } else {
            "void".to_string()
        };

        self.write_indent();
        self.write(&format!("{} {}(", ret_type, mangled_name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            let cpp_ty = self.param_type_to_cpp(&param.ty);
            self.write(&format!("{} {}", cpp_ty, param.name.name));
        }

        self.write(") {\n");
        self.indent();
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("void test_{}() {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        let cpp_ty = self.type_to_cpp(&c.ty);
        // For array types, use constexpr or static const
        match &c.ty.kind {
            crate::parser::TypeKind::Array { .. } => {
                self.write_indent();
                self.write(&format!("static const {} {} = ", cpp_ty, c.name.name));
                self.generate_expr(&c.value);
                self.write(";\n\n");
            }
            _ => {
                self.write_indent();
                self.write(&format!("constexpr {} {} = ", cpp_ty, c.name.name));
                self.generate_expr(&c.value);
                self.write(";\n\n");
            }
        }
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        self.writeln(&format!("struct {} {{", s.name.name));
        self.indent();
        for field in &s.fields {
            let cpp_ty = self.type_to_cpp(&field.ty);
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{} {} = {};", cpp_ty, field.name.name, init));
        }
        self.dedent();
        self.writeln("};");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs in C++
        self.writeln(&format!("struct {} {{", l.name.name));
        self.indent();
        for field in &l.fields {
            let cpp_ty = self.type_to_cpp(&field.ty);
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{} {} = {};", cpp_ty, field.name.name, init));
        }
        self.dedent();
        self.writeln("};");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum as a struct with a tag string and variant data
        // Each variant is modeled as a static factory method
        self.writeln(&format!("struct {} {{", e.name.name));
        self.indent();
        self.writeln("std::string tag;");

        // Collect all fields from all variants
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Tuple(types) => {
                    for (i, ty) in types.iter().enumerate() {
                        let cpp_ty = self.type_to_cpp(ty);
                        self.writeln(&format!("{} v{} = {{}};", cpp_ty, i));
                    }
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    for field in fields {
                        let cpp_ty = self.type_to_cpp(&field.ty);
                        let init = self.default_value_for_type(&field.ty);
                        self.writeln(&format!("{} {} = {};", cpp_ty, field.name.name, init));
                    }
                }
                crate::parser::EnumVariantData::Unit => {}
            }
        }
        self.writeln("");

        // Generate static factory methods for each variant
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!(
                        "static {} {}() {{ {} r; r.tag = \"{}\"; return r; }}",
                        e.name.name, variant.name.name, e.name.name, variant.name.name
                    ));
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    let params: Vec<String> = types
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| format!("{} p{}", self.type_to_cpp(ty), i))
                        .collect();
                    let assigns: Vec<String> = (0..types.len())
                        .map(|i| format!("r.v{} = p{};", i, i))
                        .collect();
                    self.writeln(&format!(
                        "static {} {}({}) {{ {} r; r.tag = \"{}\"; {} return r; }}",
                        e.name.name,
                        variant.name.name,
                        params.join(", "),
                        e.name.name,
                        variant.name.name,
                        assigns.join(" ")
                    ));
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    let params: Vec<String> = fields
                        .iter()
                        .map(|f| format!("{} {}", self.type_to_cpp(&f.ty), f.name.name))
                        .collect();
                    let assigns: Vec<String> = fields
                        .iter()
                        .map(|f| format!("r.{n} = {n};", n = f.name.name))
                        .collect();
                    self.writeln(&format!(
                        "static {} {}({}) {{ {} r; r.tag = \"{}\"; {} return r; }}",
                        e.name.name,
                        variant.name.name,
                        params.join(", "),
                        e.name.name,
                        variant.name.name,
                        assigns.join(" ")
                    ));
                }
            }
        }
        self.dedent();
        self.writeln("};");
        self.writeln("");
    }

    fn default_value_for_type(&self, ty: &ParserType) -> String {
        match &ty.kind {
            crate::parser::TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    crate::parser::PrimitiveType::Bool => "false".to_string(),
                    _ => "0".to_string(),
                }
            }
            crate::parser::TypeKind::Array { element, size } => {
                let elem_ty = self.type_to_cpp(element);
                format!("std::array<{}, {}>{{}}", elem_ty, size)
            }
            crate::parser::TypeKind::Named(ident) => {
                format!("{}{{}}", ident.name)
            }
            _ => "{}".to_string(),
        }
    }

    /// Convert a parser type to C++ type string
    fn type_to_cpp(&self, ty: &ParserType) -> String {
        match &ty.kind {
            crate::parser::TypeKind::Primitive(p) => self.primitive_to_cpp(*p),
            crate::parser::TypeKind::Array { element, size } => {
                let elem = self.type_to_cpp(element);
                format!("std::array<{}, {}>", elem, size)
            }
            crate::parser::TypeKind::Slice { element } => {
                let elem = self.type_to_cpp(element);
                format!("std::span<{}>", elem)
            }
            crate::parser::TypeKind::ArrayRef { element, size } => {
                let elem = self.type_to_cpp(element);
                format!("std::array<{}, {}>&", elem, size)
            }
            crate::parser::TypeKind::MutRef(inner) => {
                let inner_cpp = self.type_to_cpp(inner);
                format!("{}&", inner_cpp)
            }
            crate::parser::TypeKind::Ref(inner) => {
                let inner_cpp = self.type_to_cpp(inner);
                format!("const {}&", inner_cpp)
            }
            crate::parser::TypeKind::Named(ident) => ident.name.clone(),
            crate::parser::TypeKind::SelfType => "auto".to_string(),
        }
    }

    /// Convert a parser type to C++ parameter type (may differ for pass-by-reference)
    fn param_type_to_cpp(&self, ty: &ParserType) -> String {
        match &ty.kind {
            crate::parser::TypeKind::MutRef(inner) => {
                let inner_cpp = self.type_to_cpp(inner);
                format!("{}&", inner_cpp)
            }
            crate::parser::TypeKind::Ref(inner) => {
                let inner_cpp = self.type_to_cpp(inner);
                format!("const {}&", inner_cpp)
            }
            crate::parser::TypeKind::Slice { element } => {
                let elem = self.type_to_cpp(element);
                format!("std::span<{}>", elem)
            }
            crate::parser::TypeKind::Array { element, size } => {
                let elem = self.type_to_cpp(element);
                format!("std::array<{}, {}>", elem, size)
            }
            _ => self.type_to_cpp(ty),
        }
    }

    /// Convert a primitive type to C++ type string
    fn primitive_to_cpp(&self, p: crate::parser::PrimitiveType) -> String {
        use crate::parser::PrimitiveType;
        // Strip endianness - C++ types don't encode byte order
        let native = p.to_native();
        match native {
            PrimitiveType::U8 => "uint8_t".to_string(),
            PrimitiveType::U16 => "uint16_t".to_string(),
            PrimitiveType::U32 => "uint32_t".to_string(),
            PrimitiveType::U64 => "uint64_t".to_string(),
            PrimitiveType::U128 => "__uint128_t".to_string(),
            PrimitiveType::I8 => "int8_t".to_string(),
            PrimitiveType::I16 => "int16_t".to_string(),
            PrimitiveType::I32 => "int32_t".to_string(),
            PrimitiveType::I64 => "int64_t".to_string(),
            PrimitiveType::I128 => "__int128_t".to_string(),
            PrimitiveType::Bool => "bool".to_string(),
            // to_native() covers all endian variants, so this is unreachable
            _ => unreachable!("to_native() should have stripped endianness"),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        // Build return type
        let ret_type = if let Some(ret_ty) = &func.return_type {
            self.type_to_cpp(ret_ty)
        } else {
            "void".to_string()
        };

        self.write_indent();
        self.write(&format!("{} {}(", ret_type, func.name.name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            let cpp_ty = self.param_type_to_cpp(&param.ty);
            self.write(&format!("{} {}", cpp_ty, param.name.name));
        }

        self.write(") {\n");
        self.indent();
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
                // Track struct types for method resolution
                if let Some(ty) = ty
                    && let crate::parser::TypeKind::Named(type_ident) = &ty.kind
                {
                    self.var_types
                        .insert(name.name.clone(), type_ident.name.clone());
                }

                // Infer type from constructor calls
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
                if let Some(ty) = ty {
                    let cpp_ty = self.type_to_cpp(ty);
                    self.write(&format!("{} {}", cpp_ty, name.name));
                } else if let Some(init) = init {
                    // Use auto when type is not specified
                    let _ = init;
                    self.write(&format!("auto {}", name.name));
                } else {
                    self.write(&format!("auto {}", name.name));
                }

                if let Some(init) = init {
                    self.write(" = ");
                    self.generate_expr(init);
                } else if let Some(ty) = ty {
                    // Default initialize
                    let init_val = self.default_value_for_type(ty);
                    self.write(&format!(" = {}", init_val));
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
                        && let ExprKind::Slice { array, start, .. } = &inner.kind
                    {
                        let little_endian = endian == crate::parser::Endianness::Little;
                        let writer_fn = match (p.to_native(), little_endian) {
                            (crate::parser::PrimitiveType::U16, false)
                            | (crate::parser::PrimitiveType::I16, false) => "write_u16be",
                            (crate::parser::PrimitiveType::U16, true)
                            | (crate::parser::PrimitiveType::I16, true) => "write_u16le",
                            (crate::parser::PrimitiveType::U32, false)
                            | (crate::parser::PrimitiveType::I32, false) => "write_u32be",
                            (crate::parser::PrimitiveType::U32, true)
                            | (crate::parser::PrimitiveType::I32, true) => "write_u32le",
                            (crate::parser::PrimitiveType::U64, false)
                            | (crate::parser::PrimitiveType::I64, false) => "write_u64be",
                            (crate::parser::PrimitiveType::U64, true)
                            | (crate::parser::PrimitiveType::I64, true) => "write_u64le",
                            (crate::parser::PrimitiveType::U128, false)
                            | (crate::parser::PrimitiveType::I128, false) => "write_u128be",
                            (crate::parser::PrimitiveType::U128, true)
                            | (crate::parser::PrimitiveType::I128, true) => "write_u128le",
                            _ => "write_u32be",
                        };
                        self.write_indent();
                        self.write(&format!("{}(", writer_fn));
                        self.generate_expr(array);
                        self.write(".data() + ");
                        self.generate_expr(start);
                        self.write(", ");
                        self.generate_expr(value);
                        self.write(");\n");
                        return;
                    }
                }

                // Check for slice assignment: buf[start..end] = value
                if let ExprKind::Slice {
                    array, start, end, ..
                } = &target.kind
                {
                    self.write_indent();
                    self.write("copy_to_slice(");
                    self.generate_expr(array);
                    self.write(", ");
                    self.generate_expr(start);
                    self.write(", ");
                    self.generate_expr(end);
                    self.write(", ");
                    self.generate_expr(value);
                    self.write(");\n");
                    return;
                }

                self.write_indent();
                self.generate_expr(target);
                self.write(" = ");
                self.generate_expr(value);
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
                    BinaryOp::Shr => ">>=",
                    _ => "=",
                };
                self.write(&format!(" {} ", op_str));
                self.generate_expr(value);
                self.write(";\n");
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
                self.write(&format!("for (auto {} = ", var.name));
                self.generate_expr(start);
                self.write(&format!(
                    "; {} {} ",
                    var.name,
                    if *inclusive { "<=" } else { "<" }
                ));
                self.generate_expr(end);
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
                // Use appropriate suffixes for large values
                if *n > u64::MAX as u128 {
                    // __uint128_t literal: construct from two 64-bit halves
                    let hi = (*n >> 64) as u64;
                    let lo = *n as u64;
                    self.write(&format!(
                        "((__uint128_t(UINT64_C({})) << 64) | __uint128_t(UINT64_C({})))",
                        hi, lo
                    ));
                } else if *n > u32::MAX as u128 {
                    self.write(&format!("UINT64_C({})", n));
                } else {
                    self.write(&format!("{}", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                let escaped = escape_cpp_string(s);
                self.write(&format!("string_to_bytes(\"{}\", {})", escaped, s.len()));
            }
            ExprKind::Bytes(s) => {
                let escaped = escape_cpp_string(s);
                self.write(&format!("string_to_bytes(\"{}\", {})", escaped, s.len()));
            }
            ExprKind::Hex(h) => {
                self.write(&format!("hex_to_bytes(\"{}\")", h));
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
                // Generate a span view of the subrange
                self.write("std::span<uint8_t>(");
                self.generate_expr(array);
                self.write(".data() + ");
                self.generate_expr(start);
                self.write(", ");
                self.generate_expr(end);
                self.write(" - ");
                self.generate_expr(start);
                self.write(")");
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

                // Check for method calls like slice.len() or reader.read_u32()
                if let ExprKind::Field { object, field } = &func.kind {
                    if field.name == "len" && args.is_empty() {
                        // Convert .len() to .size()
                        self.generate_expr(object);
                        self.write(".size()");
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
                        self.write("[&]() { ");
                        for field_info in &fields {
                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty)
                            {
                                self.write(&format!("{}.{} = ", var_ident.name, field_info.name));
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
                            self.write("[&]() { ");
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
                            self.write("}()");
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
                    self.write("std::vector<uint8_t>{}");
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
                        self.write("std::vector<uint8_t>{");
                    } else {
                        self.write("std::vector<uint32_t>{");
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
                self.write("std::vector<uint8_t>(");
                self.generate_expr(count);
                self.write(", ");
                self.generate_expr(value);
                self.write(")");
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in C++ function args: just pass the value
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
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
                    self.write(&format!(".{} = ", field_name.name));
                    self.generate_expr(value);
                }
                self.write("}");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
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
                if args.is_empty() {
                    self.write(&format!("{}::{}()", enum_name.name, variant_name.name));
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
                // Generate match as an IIFE with if-else chain
                self.write("[&]() -> auto { auto __match = ");
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
                // Add a default unreachable to satisfy the compiler
                self.write(" else { return decltype(");
                // Use the first arm's body type as fallback
                if let Some(first_arm) = arms.first() {
                    self.generate_expr(&first_arm.body);
                } else {
                    self.write("0");
                }
                self.write("){}; }");
                self.write(" }()");
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
                self.write("if (true)");
            }
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("if ({} == ", scrutinee));
                self.generate_expr(lit_expr);
                self.write(")");
            }
            PatternKind::Ident(ident) => {
                // Binding pattern - always matches, bind the value
                self.write(&format!(
                    "if ([&]() {{ auto {} = {}; return true; }}())",
                    ident.name, scrutinee
                ));
            }
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!(
                    "if ({}.tag == \"{}\")",
                    scrutinee, variant_name.name
                ));
            }
            PatternKind::Tuple(_) => {
                self.write("if (true)"); // Simplified
            }
            PatternKind::Or(patterns) => {
                self.write("if (");
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
                self.write(&format!("{} == ", scrutinee));
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(_) => self.write("true"),
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!("{}.tag == \"{}\"", scrutinee, variant_name.name));
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
                let little_endian = endian == Endianness::Little;
                let native = p.to_native();

                // Check if source is a byte sequence (for from_bytes conversion)
                if is_byte_sequence_expr(expr) {
                    let reader_fn = match (native, little_endian) {
                        (PrimitiveType::U16 | PrimitiveType::I16, false) => "read_u16be",
                        (PrimitiveType::U16 | PrimitiveType::I16, true) => "read_u16le",
                        (PrimitiveType::U32 | PrimitiveType::I32, false) => "read_u32be",
                        (PrimitiveType::U32 | PrimitiveType::I32, true) => "read_u32le",
                        (PrimitiveType::U64 | PrimitiveType::I64, false) => "read_u64be",
                        (PrimitiveType::U64 | PrimitiveType::I64, true) => "read_u64le",
                        (PrimitiveType::U128 | PrimitiveType::I128, false) => "read_u128be",
                        (PrimitiveType::U128 | PrimitiveType::I128, true) => "read_u128le",
                        _ => "read_u32be",
                    };
                    // Call the read helper on the data pointer
                    self.write("[&]() { auto __s = ");
                    self.generate_expr(expr);
                    self.write(&format!("; return {}(__s.data()); }}()", reader_fn));
                    return;
                }

                // Integer to integer with different endianness - just mask to width
                let cpp_ty = self.primitive_to_cpp(native);
                self.write(&format!("static_cast<{}>(", cpp_ty));
                self.generate_expr(expr);
                self.write(")");
                return;
            }
        }

        // Check for integer to byte array cast (e.g., value as u8[4])
        if let TypeKind::Array { element, size } = &ty.kind
            && let TypeKind::Primitive(PrimitiveType::U8) = &element.kind
        {
            let (little_endian, bits) = self.get_expr_endianness_info(expr);
            let writer_fn = match (bits, little_endian) {
                (16, false) => "write_u16be",
                (16, true) => "write_u16le",
                (32, false) => "write_u32be",
                (32, true) => "write_u32le",
                (64, false) => "write_u64be",
                (64, true) => "write_u64le",
                (128, false) => "write_u128be",
                (128, true) => "write_u128le",
                _ => "write_u32le",
            };

            self.write(&format!(
                "[&]() {{ std::array<uint8_t, {}> __a{{}}; {}(__a.data(), ",
                size, writer_fn
            ));
            // If the expression is a cast, unwrap it to get the raw value
            if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                self.generate_expr(inner);
            } else {
                self.generate_expr(expr);
            }
            self.write("); return __a; }()");
            return;
        }

        // Standard casts - use static_cast
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let cpp_ty = self.primitive_to_cpp(*p);
                self.write(&format!("static_cast<{}>(", cpp_ty));
                self.generate_expr(expr);
                self.write(")");
            }
            _ => {
                // For non-primitive types, just generate the expression
                self.generate_expr(expr);
            }
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
        ExprKind::Index { .. } => false,
        ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Paren(inner) => {
            is_byte_sequence_expr(inner)
        }
        ExprKind::Ident(_) => true,
        ExprKind::Field { .. } => true,
        _ => false,
    }
}

impl Default for CppGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for CppGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();

        // Pre-pass: collect struct info
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

        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("");

        self.generate_runtime();

        if self.include_tests {
            self.generate_test_runtime();
        }

        // Forward declare structs (so functions can reference them)
        for item in &ast.ast.items {
            if let ItemKind::Struct(s) = &item.kind {
                self.writeln(&format!("struct {};", s.name.name));
            }
            if let ItemKind::Enum(e) = &item.kind {
                self.writeln(&format!("struct {};", e.name.name));
            }
        }
        self.writeln("");

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

        // Generate main() with test runner if tests are included
        if self.include_tests {
            self.writeln("int main() {");
            self.indent();
            self.writeln("int __passed = 0;");
            self.writeln("int __failed = 0;");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("__test_name = \"{}\";", name));
                self.writeln("__test_failures = 0;");
                self.writeln("try {");
                self.indent();
                self.writeln(&format!("test_{}();", name));
                self.writeln("if (__test_failures == 0) {");
                self.indent();
                self.writeln(&format!("std::cout << \"PASS: {}\" << std::endl;", name));
                self.writeln("__passed++;");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("std::cout << \"FAIL: {}\" << std::endl;", name));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("} catch (const std::exception& e) {");
                self.indent();
                self.writeln(&format!(
                    "std::cout << \"FAIL: {} - \" << e.what() << std::endl;",
                    name
                ));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("std::cout << std::endl;");
            self.writeln(
                "std::cout << __passed << \" passed, \" << __failed << \" failed\" << std::endl;",
            );
            self.writeln("return __failed == 0 ? 0 : 1;");
            self.dedent();
            self.writeln("}");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "cpp"
    }

    fn language_name(&self) -> &'static str {
        "C++"
    }
}

fn escape_cpp_string(s: &str) -> String {
    let mut result = String::new();
    for c in s.chars() {
        match c {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '\0' => result.push_str("\\0"),
            _ => result.push(c),
        }
    }
    result
}
