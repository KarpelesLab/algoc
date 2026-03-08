//! Objective-C code generator
//!
//! Generates Objective-C code from the analyzed AST.
//! Since Objective-C is a superset of C, the output is mostly C code with
//! Foundation imports and @autoreleasepool in main. Uses C arrays, C structs,
//! and C functions throughout for simplicity and performance.

use super::CodeGenerator;
use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;
use crate::parser::{
    Ast, BinaryOp, Block, BuiltinFunc, Expr, ExprKind, Function, ItemKind, Stmt, StmtKind,
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

/// Objective-C code generator
pub struct ObjCGenerator {
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
    /// Variables that are pointers (from &mut / & parameters), needing -> instead of .
    pointer_vars: HashSet<String>,
}

impl ObjCGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            pointer_vars: HashSet::new(),
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

    /// Map a parser type to a C type string
    #[allow(clippy::only_used_in_recursion)]
    fn type_to_c(&self, ty: &ParserType) -> String {
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(p) => {
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
                    // Endian variants map to their native type
                    _ => "uint32_t".to_string(),
                }
            }
            TypeKind::Array { element, size } => {
                // We'll return the element type; the caller handles the array dimension
                format!("{}[{}]", self.type_to_c(element), size)
            }
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                format!("{}*", self.type_to_c(element))
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => match &inner.kind {
                TypeKind::Array { element, .. }
                | TypeKind::Slice { element }
                | TypeKind::ArrayRef { element, .. } => {
                    format!("{}*", self.type_to_c(element))
                }
                _ => format!("{}*", self.type_to_c(inner)),
            },
            TypeKind::Named(ident) => {
                format!("struct {}", ident.name)
            }
            TypeKind::SelfType => "void*".to_string(),
        }
    }

    /// Get the base C type string for a type (without array dimensions)
    fn type_to_c_base(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Array { element, .. } => self.type_to_c_base(element),
            _ => self.type_to_c(ty),
        }
    }

    /// Get array dimensions suffix if the type is an array, empty string otherwise
    fn type_array_suffix(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Array { size, .. } => format!("[{}]", size),
            _ => String::new(),
        }
    }

    /// Get the default initializer for a C type
    fn default_value_for_type(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(_) => "0".to_string(),
            TypeKind::Array { .. } => "{0}".to_string(),
            TypeKind::Named(_) => "{0}".to_string(),
            _ => "0".to_string(),
        }
    }

    /// Check if a parameter type results in a pointer to a struct/primitive (not array/slice)
    /// and thus needs -> for field access instead of .
    fn is_pointer_param(ty: &ParserType) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                matches!(
                    inner.kind,
                    TypeKind::Named(_) | TypeKind::Primitive(_) | TypeKind::SelfType
                )
            }
            _ => false,
        }
    }

    /// Populate pointer_vars from function parameters
    fn collect_pointer_params(&mut self, func: &Function) {
        self.pointer_vars.clear();
        for param in &func.params {
            if Self::is_pointer_param(&param.ty) {
                self.pointer_vars.insert(param.name.name.clone());
            }
        }
    }

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        self.writeln("// ---- Runtime Helpers ----");
        self.writeln("");

        // memcpy_bytes helper
        self.writeln("static void __memcpy_bytes(uint8_t *dst, const uint8_t *src, size_t len) {");
        self.indent();
        self.writeln("memcpy(dst, src, len);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Reader struct and functions
        self.writeln("typedef struct Reader {");
        self.indent();
        self.writeln("const uint8_t *data;");
        self.writeln("size_t len;");
        self.writeln("size_t pos;");
        self.dedent();
        self.writeln("} Reader;");
        self.writeln("");

        self.writeln("static Reader Reader_new(const uint8_t *data, size_t len) {");
        self.indent();
        self.writeln("Reader r = { data, len, 0 };");
        self.writeln("return r;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint8_t Reader_read_u8(Reader *r) {");
        self.indent();
        self.writeln("return r->data[r->pos++];");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u16be/le
        self.writeln("static uint16_t Reader_read_u16be(Reader *r) {");
        self.indent();
        self.writeln(
            "uint16_t v = ((uint16_t)r->data[r->pos] << 8) | (uint16_t)r->data[r->pos + 1];",
        );
        self.writeln("r->pos += 2;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint16_t Reader_read_u16le(Reader *r) {");
        self.indent();
        self.writeln(
            "uint16_t v = ((uint16_t)r->data[r->pos + 1] << 8) | (uint16_t)r->data[r->pos];",
        );
        self.writeln("r->pos += 2;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint16_t Reader_read_u16(Reader *r) { return Reader_read_u16be(r); }");
        self.writeln("");

        // read_u32be/le
        self.writeln("static uint32_t Reader_read_u32be(Reader *r) {");
        self.indent();
        self.writeln("uint32_t v = ((uint32_t)r->data[r->pos] << 24) | ((uint32_t)r->data[r->pos + 1] << 16) | ((uint32_t)r->data[r->pos + 2] << 8) | (uint32_t)r->data[r->pos + 3];");
        self.writeln("r->pos += 4;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint32_t Reader_read_u32le(Reader *r) {");
        self.indent();
        self.writeln("uint32_t v = ((uint32_t)r->data[r->pos + 3] << 24) | ((uint32_t)r->data[r->pos + 2] << 16) | ((uint32_t)r->data[r->pos + 1] << 8) | (uint32_t)r->data[r->pos];");
        self.writeln("r->pos += 4;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint32_t Reader_read_u32(Reader *r) { return Reader_read_u32be(r); }");
        self.writeln("");

        // read_u64be/le
        self.writeln("static uint64_t Reader_read_u64be(Reader *r) {");
        self.indent();
        self.writeln("uint64_t v = 0;");
        self.writeln("for (int i = 0; i < 8; i++) v = (v << 8) | r->data[r->pos + i];");
        self.writeln("r->pos += 8;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint64_t Reader_read_u64le(Reader *r) {");
        self.indent();
        self.writeln("uint64_t v = 0;");
        self.writeln("for (int i = 7; i >= 0; i--) v = (v << 8) | r->data[r->pos + i];");
        self.writeln("r->pos += 8;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static uint64_t Reader_read_u64(Reader *r) { return Reader_read_u64be(r); }");
        self.writeln("");

        // read_bytes
        self.writeln("static const uint8_t* Reader_read_bytes(Reader *r, size_t count) {");
        self.indent();
        self.writeln("const uint8_t *ptr = r->data + r->pos;");
        self.writeln("r->pos += count;");
        self.writeln("return ptr;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_chunk
        self.writeln(
            "static const uint8_t* Reader_read_chunk(Reader *r, size_t max_size, size_t *out_len) {",
        );
        self.indent();
        self.writeln("size_t remaining = r->len - r->pos;");
        self.writeln("size_t count = max_size < remaining ? max_size : remaining;");
        self.writeln("const uint8_t *ptr = r->data + r->pos;");
        self.writeln("r->pos += count;");
        self.writeln("*out_len = count;");
        self.writeln("return ptr;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // eof
        self.writeln("static bool Reader_eof(Reader *r) { return r->pos >= r->len; }");
        self.writeln("");

        // Writer struct and functions
        self.writeln("typedef struct Writer {");
        self.indent();
        self.writeln("uint8_t *data;");
        self.writeln("size_t len;");
        self.writeln("size_t pos;");
        self.dedent();
        self.writeln("} Writer;");
        self.writeln("");

        self.writeln("static Writer Writer_new(uint8_t *data, size_t len) {");
        self.indent();
        self.writeln("Writer w = { data, len, 0 };");
        self.writeln("return w;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void Writer_write_u8(Writer *w, uint8_t v) {");
        self.indent();
        self.writeln("w->data[w->pos++] = v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u16be/le
        self.writeln("static void Writer_write_u16be(Writer *w, uint16_t v) {");
        self.indent();
        self.writeln("w->data[w->pos++] = (uint8_t)(v >> 8);");
        self.writeln("w->data[w->pos++] = (uint8_t)(v & 0xFF);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void Writer_write_u16le(Writer *w, uint16_t v) {");
        self.indent();
        self.writeln("w->data[w->pos++] = (uint8_t)(v & 0xFF);");
        self.writeln("w->data[w->pos++] = (uint8_t)(v >> 8);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln(
            "static void Writer_write_u16(Writer *w, uint16_t v) { Writer_write_u16be(w, v); }",
        );
        self.writeln("");

        // write_u32be/le
        self.writeln("static void Writer_write_u32be(Writer *w, uint32_t v) {");
        self.indent();
        self.writeln("w->data[w->pos++] = (uint8_t)(v >> 24);");
        self.writeln("w->data[w->pos++] = (uint8_t)(v >> 16);");
        self.writeln("w->data[w->pos++] = (uint8_t)(v >> 8);");
        self.writeln("w->data[w->pos++] = (uint8_t)(v & 0xFF);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void Writer_write_u32le(Writer *w, uint32_t v) {");
        self.indent();
        self.writeln("w->data[w->pos++] = (uint8_t)(v & 0xFF);");
        self.writeln("w->data[w->pos++] = (uint8_t)(v >> 8);");
        self.writeln("w->data[w->pos++] = (uint8_t)(v >> 16);");
        self.writeln("w->data[w->pos++] = (uint8_t)(v >> 24);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln(
            "static void Writer_write_u32(Writer *w, uint32_t v) { Writer_write_u32be(w, v); }",
        );
        self.writeln("");

        // write_u64be/le
        self.writeln("static void Writer_write_u64be(Writer *w, uint64_t v) {");
        self.indent();
        self.writeln(
            "for (int i = 7; i >= 0; i--) { w->data[w->pos++] = (uint8_t)(v >> (i * 8)); }",
        );
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void Writer_write_u64le(Writer *w, uint64_t v) {");
        self.indent();
        self.writeln(
            "for (int i = 0; i < 8; i++) { w->data[w->pos++] = (uint8_t)(v >> (i * 8)); }",
        );
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln(
            "static void Writer_write_u64(Writer *w, uint64_t v) { Writer_write_u64be(w, v); }",
        );
        self.writeln("");

        // write_bytes
        self.writeln(
            "static void Writer_write_bytes(Writer *w, const uint8_t *data, size_t len) {",
        );
        self.indent();
        self.writeln("memcpy(w->data + w->pos, data, len);");
        self.writeln("w->pos += len;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // 128-bit helpers (using GCC __uint128_t)
        self.writeln("static __uint128_t __read_u128be(const uint8_t *buf) {");
        self.indent();
        self.writeln("__uint128_t v = 0;");
        self.writeln("for (int i = 0; i < 16; i++) v = (v << 8) | buf[i];");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static __uint128_t __read_u128le(const uint8_t *buf) {");
        self.indent();
        self.writeln("__uint128_t v = 0;");
        self.writeln("for (int i = 15; i >= 0; i--) v = (v << 8) | buf[i];");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void __write_u128be(uint8_t *buf, __uint128_t v) {");
        self.indent();
        self.writeln("for (int i = 15; i >= 0; i--) { buf[i] = (uint8_t)(v & 0xFF); v >>= 8; }");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("static void __write_u128le(uint8_t *buf, __uint128_t v) {");
        self.indent();
        self.writeln("for (int i = 0; i < 16; i++) { buf[i] = (uint8_t)(v & 0xFF); v >>= 8; }");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Generate test runtime helpers
    fn generate_test_runtime(&mut self) {
        self.writeln("// ---- Test Helpers ----");
        self.writeln("");
        self.writeln("static int __test_failures = 0;");
        self.writeln("static const char *__test_name = \"\";");
        self.writeln("");
        self.writeln("static void algoc_assert(bool condition) {");
        self.indent();
        self.writeln("if (!condition) {");
        self.indent();
        self.writeln("__test_failures++;");
        self.writeln("printf(\"  ASSERTION FAILED in %s\\n\", __test_name);");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_ast(&mut self, ast: &Ast) {
        // Pass 1: Emit type definitions (structs, enums, layouts, consts)
        for item in &ast.items {
            match &item.kind {
                ItemKind::Struct(s) => self.generate_struct(s),
                ItemKind::Layout(l) => self.generate_layout(l),
                ItemKind::Enum(e) => self.generate_enum(e),
                ItemKind::Const(c) => self.generate_const(c),
                _ => {}
            }
        }

        // Pass 2: Emit forward declarations for all functions and methods
        self.generate_forward_declarations(ast);

        // Pass 3: Emit function/method/test definitions
        for item in &ast.items {
            match &item.kind {
                ItemKind::Function(func) => self.generate_function(func),
                ItemKind::Impl(impl_def) => {
                    for method in &impl_def.methods {
                        self.generate_method(&impl_def.target.name, method);
                    }
                }
                ItemKind::Test(test) => {
                    if self.include_tests {
                        self.generate_test(test);
                    }
                }
                ItemKind::Use(_)
                | ItemKind::Interface(_)
                | ItemKind::Struct(_)
                | ItemKind::Layout(_)
                | ItemKind::Enum(_)
                | ItemKind::Const(_) => {
                    // Already handled in pass 1 or not needed
                }
            }
        }
    }

    /// Generate forward declarations for all functions and methods
    fn generate_forward_declarations(&mut self, ast: &Ast) {
        let mut has_decls = false;

        for item in &ast.items {
            match &item.kind {
                ItemKind::Function(func) => {
                    self.generate_forward_decl(func, None);
                    has_decls = true;
                }
                ItemKind::Impl(impl_def) => {
                    for method in &impl_def.methods {
                        self.generate_forward_decl(method, Some(&impl_def.target.name));
                        has_decls = true;
                    }
                }
                ItemKind::Test(test) => {
                    if self.include_tests {
                        self.writeln(&format!("static void test_{}(void);", test.name.name));
                        has_decls = true;
                    }
                }
                _ => {}
            }
        }

        if has_decls {
            self.writeln("");
        }
    }

    /// Generate a forward declaration for a function or method
    fn generate_forward_decl(&mut self, func: &Function, struct_name: Option<&str>) {
        let func_name = if let Some(sn) = struct_name {
            format!("{}__{}", sn, func.name.name)
        } else {
            func.name.name.clone()
        };

        // Return type - resolve Self to actual struct name
        let ret_type = if let Some(ref rt) = func.return_type {
            match &rt.kind {
                crate::parser::TypeKind::Named(ident)
                    if ident.name == "Self" && struct_name.is_some() =>
                {
                    format!("struct {}", struct_name.unwrap())
                }
                crate::parser::TypeKind::SelfType if struct_name.is_some() => {
                    format!("struct {}", struct_name.unwrap())
                }
                crate::parser::TypeKind::Named(ident) => format!("struct {}", ident.name),
                crate::parser::TypeKind::Array { .. } => "void".to_string(),
                _ => self.type_to_c(rt),
            }
        } else {
            "void".to_string()
        };

        self.write_indent();
        self.write(&format!("{} {}(", ret_type, func_name));

        let mut first = true;
        for param in &func.params {
            if !first {
                self.write(", ");
            }
            first = false;

            if param.name.name == "self" {
                if let Some(sn) = struct_name {
                    self.write(&format!("struct {}* self", sn));
                } else {
                    self.write("void* self");
                }
            } else {
                let base_type = self.type_to_c_base(&param.ty);
                let arr_suffix = self.type_array_suffix(&param.ty);
                if arr_suffix.is_empty() {
                    match &param.ty.kind {
                        crate::parser::TypeKind::Slice { element }
                        | crate::parser::TypeKind::ArrayRef { element, .. } => {
                            let elem_type = self.type_to_c(element);
                            self.write(&format!("{}* {}", elem_type, param.name.name));
                        }
                        crate::parser::TypeKind::MutRef(inner)
                        | crate::parser::TypeKind::Ref(inner) => match &inner.kind {
                            crate::parser::TypeKind::Slice { element }
                            | crate::parser::TypeKind::ArrayRef { element, .. } => {
                                let elem_type = self.type_to_c(element);
                                self.write(&format!("{}* {}", elem_type, param.name.name));
                            }
                            crate::parser::TypeKind::Array { .. } => {
                                let base = self.type_to_c_base(inner);
                                self.write(&format!("{}* {}", base, param.name.name));
                            }
                            _ => {
                                let inner_type = self.type_to_c(inner);
                                self.write(&format!("{}* {}", inner_type, param.name.name));
                            }
                        },
                        crate::parser::TypeKind::Named(ident) => {
                            self.write(&format!("struct {} {}", ident.name, param.name.name));
                        }
                        _ => {
                            self.write(&format!("{} {}", base_type, param.name.name));
                        }
                    }
                } else {
                    self.write(&format!("{}* {}", base_type, param.name.name));
                }
            }
        }

        if first {
            self.write("void");
        }

        self.write(");\n");
    }

    fn generate_function(&mut self, func: &Function) {
        self.var_types.clear();

        // Return type
        let ret_type = if let Some(ref rt) = func.return_type {
            self.type_to_c(rt)
        } else {
            "void".to_string()
        };

        // Check if return type is an array type (needs special handling)
        let ret_is_array = if let Some(ref rt) = func.return_type {
            matches!(rt.kind, crate::parser::TypeKind::Array { .. })
        } else {
            false
        };

        self.write_indent();
        if ret_is_array {
            // Can't return arrays directly in C; for now emit the base type
            // In practice the transpiler likely doesn't produce functions returning arrays
            self.write(&format!("{} {}(", ret_type, func.name.name));
        } else {
            self.write(&format!("{} {}(", ret_type, func.name.name));
        }

        // Parameters
        if func.params.is_empty() {
            self.write("void");
        } else {
            for (i, param) in func.params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                let base_type = self.type_to_c_base(&param.ty);
                let arr_suffix = self.type_array_suffix(&param.ty);
                if arr_suffix.is_empty() {
                    // Check if the param type is a reference/slice → pass as pointer
                    match &param.ty.kind {
                        crate::parser::TypeKind::Slice { element }
                        | crate::parser::TypeKind::ArrayRef { element, .. } => {
                            let elem_type = self.type_to_c(element);
                            self.write(&format!("{}* {}", elem_type, param.name.name));
                        }
                        crate::parser::TypeKind::MutRef(inner)
                        | crate::parser::TypeKind::Ref(inner) => {
                            // For references to slices/arrays, inner already maps to a pointer type
                            // (e.g. &mut [u8] -> Slice{u8} -> "uint8_t*"), so don't add another "*"
                            match &inner.kind {
                                crate::parser::TypeKind::Slice { element }
                                | crate::parser::TypeKind::ArrayRef { element, .. } => {
                                    let elem_type = self.type_to_c(element);
                                    self.write(&format!("{}* {}", elem_type, param.name.name));
                                }
                                crate::parser::TypeKind::Array { .. } => {
                                    let base = self.type_to_c_base(inner);
                                    self.write(&format!("{}* {}", base, param.name.name));
                                }
                                _ => {
                                    let inner_type = self.type_to_c(inner);
                                    self.write(&format!("{}* {}", inner_type, param.name.name));
                                }
                            }
                            // Track struct type for mutable/immutable references
                            if let crate::parser::TypeKind::Named(ident) = &inner.kind {
                                self.var_types
                                    .insert(param.name.name.clone(), ident.name.clone());
                            }
                        }
                        crate::parser::TypeKind::Named(ident) => {
                            self.write(&format!("struct {} {}", ident.name, param.name.name));
                            self.var_types
                                .insert(param.name.name.clone(), ident.name.clone());
                        }
                        _ => {
                            self.write(&format!("{} {}", base_type, param.name.name));
                        }
                    }
                } else {
                    // Array parameters decay to pointers in C
                    self.write(&format!("{}* {}", base_type, param.name.name));
                }
            }
        }

        self.write(") {\n");
        self.indent();
        self.collect_pointer_params(func);
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_method(&mut self, struct_name: &str, func: &crate::parser::Function) {
        self.var_types.clear();

        let mangled_name = format!("{}__{}", struct_name, func.name.name);

        // Return type - resolve Self to the actual struct name
        let ret_type = if let Some(ref rt) = func.return_type {
            match &rt.kind {
                crate::parser::TypeKind::Named(ident) if ident.name == "Self" => {
                    format!("struct {}", struct_name)
                }
                crate::parser::TypeKind::Named(ident) => format!("struct {}", ident.name),
                crate::parser::TypeKind::SelfType => format!("struct {}", struct_name),
                _ => self.type_to_c(rt),
            }
        } else {
            "void".to_string()
        };

        self.write_indent();
        self.write(&format!("{} {}(", ret_type, mangled_name));

        // Parameters: first param is self (pointer to struct)
        let mut param_idx = 0;
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            // 'self' parameter → pointer to struct
            if param.name.name == "self" {
                self.write(&format!("struct {}* self", struct_name));
            } else {
                let base_type = self.type_to_c_base(&param.ty);
                let arr_suffix = self.type_array_suffix(&param.ty);
                if arr_suffix.is_empty() {
                    match &param.ty.kind {
                        crate::parser::TypeKind::Slice { element }
                        | crate::parser::TypeKind::ArrayRef { element, .. } => {
                            let elem_type = self.type_to_c(element);
                            self.write(&format!("{}* {}", elem_type, param.name.name));
                        }
                        crate::parser::TypeKind::MutRef(inner)
                        | crate::parser::TypeKind::Ref(inner) => {
                            // For references to slices/arrays, inner already maps to a pointer type
                            // (e.g. &mut [u8] -> Slice{u8} -> "uint8_t*"), so don't add another "*"
                            match &inner.kind {
                                crate::parser::TypeKind::Slice { element }
                                | crate::parser::TypeKind::ArrayRef { element, .. } => {
                                    let elem_type = self.type_to_c(element);
                                    self.write(&format!("{}* {}", elem_type, param.name.name));
                                }
                                crate::parser::TypeKind::Array { .. } => {
                                    let base = self.type_to_c_base(inner);
                                    self.write(&format!("{}* {}", base, param.name.name));
                                }
                                _ => {
                                    let inner_type = self.type_to_c(inner);
                                    self.write(&format!("{}* {}", inner_type, param.name.name));
                                }
                            }
                            // Track struct type for mutable/immutable references
                            if let crate::parser::TypeKind::Named(ident) = &inner.kind {
                                self.var_types
                                    .insert(param.name.name.clone(), ident.name.clone());
                            }
                        }
                        crate::parser::TypeKind::Named(ident) => {
                            self.write(&format!("struct {} {}", ident.name, param.name.name));
                            self.var_types
                                .insert(param.name.name.clone(), ident.name.clone());
                        }
                        _ => {
                            self.write(&format!("{} {}", base_type, param.name.name));
                        }
                    }
                } else {
                    self.write(&format!("{}* {}", base_type, param.name.name));
                }
            }
            param_idx += 1;
        }

        if param_idx == 0 {
            self.write("void");
        }

        self.write(") {\n");
        self.indent();
        self.collect_pointer_params(func);
        // 'self' is always a pointer in methods
        self.pointer_vars.insert("self".to_string());
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.var_types.clear();
        self.writeln(&format!("static void test_{}(void) {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        use crate::parser::TypeKind;
        match &c.ty.kind {
            TypeKind::Array { element, size } => {
                let elem_type = self.type_to_c(element);
                self.write_indent();
                self.write(&format!(
                    "static const {} {}[{}] = ",
                    elem_type, c.name.name, size
                ));
                self.generate_expr(&c.value);
                self.write(";\n\n");
            }
            _ => {
                let type_str = self.type_to_c(&c.ty);
                self.write_indent();
                self.write(&format!("static const {} {} = ", type_str, c.name.name));
                self.generate_expr(&c.value);
                self.write(";\n\n");
            }
        }
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Use tagged struct so both `StructName` and `struct StructName` work
        self.writeln(&format!("typedef struct {} {{", s.name.name));
        self.indent();
        for field in &s.fields {
            let base_type = self.type_to_c_base(&field.ty);
            let arr_suffix = self.type_array_suffix(&field.ty);
            self.writeln(&format!("{} {}{};", base_type, field.name.name, arr_suffix));
        }
        self.dedent();
        self.writeln(&format!("}} {};", s.name.name));
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs in C - use tagged struct
        self.writeln(&format!("typedef struct {} {{", l.name.name));
        self.indent();
        for field in &l.fields {
            let base_type = self.type_to_c_base(&field.ty);
            let arr_suffix = self.type_array_suffix(&field.ty);
            self.writeln(&format!("{} {}{};", base_type, field.name.name, arr_suffix));
        }
        self.dedent();
        self.writeln(&format!("}} {};", l.name.name));
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum as a tagged union
        // First, the tag enum
        self.writeln("typedef enum {");
        self.indent();
        for (i, variant) in e.variants.iter().enumerate() {
            let comma = if i < e.variants.len() - 1 { "," } else { "" };
            self.writeln(&format!("{}__{}{}", e.name.name, variant.name.name, comma));
        }
        self.dedent();
        self.writeln(&format!("}} {}_Tag;", e.name.name));
        self.writeln("");

        // Then the tagged union struct
        self.writeln("typedef struct {");
        self.indent();
        self.writeln(&format!("{}_Tag tag;", e.name.name));

        // Union for data
        let has_data = e
            .variants
            .iter()
            .any(|v| !matches!(v.data, crate::parser::EnumVariantData::Unit));
        if has_data {
            self.writeln("union {");
            self.indent();
            for variant in &e.variants {
                match &variant.data {
                    crate::parser::EnumVariantData::Unit => {}
                    crate::parser::EnumVariantData::Tuple(types) => {
                        self.writeln("struct {");
                        self.indent();
                        for (j, ty) in types.iter().enumerate() {
                            let type_str = self.type_to_c(ty);
                            self.writeln(&format!("{} v{};", type_str, j));
                        }
                        self.dedent();
                        self.writeln(&format!("}} {};", variant.name.name));
                    }
                    crate::parser::EnumVariantData::Struct(fields) => {
                        self.writeln("struct {");
                        self.indent();
                        for f in fields {
                            let type_str = self.type_to_c(&f.ty);
                            self.writeln(&format!("{} {};", type_str, f.name.name));
                        }
                        self.dedent();
                        self.writeln(&format!("}} {};", variant.name.name));
                    }
                }
            }
            self.dedent();
            self.writeln("} data;");
        }
        self.dedent();
        self.writeln(&format!("}} {};", e.name.name));
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

                if let Some(ty) = ty {
                    let base_type = self.type_to_c_base(ty);
                    let arr_suffix = self.type_array_suffix(ty);

                    if !arr_suffix.is_empty() {
                        // Array declaration
                        self.write_indent();
                        self.write(&format!("{} {}{}", base_type, name.name, arr_suffix));
                        if let Some(init) = init {
                            self.write(" = ");
                            self.generate_expr(init);
                        } else {
                            self.write(" = {0}");
                        }
                        self.write(";\n");
                    } else {
                        match &ty.kind {
                            crate::parser::TypeKind::Named(ident) => {
                                // Struct type
                                self.write_indent();
                                self.write(&format!("struct {} {}", ident.name, name.name));
                                if let Some(init) = init {
                                    self.write(" = ");
                                    self.generate_expr(init);
                                } else {
                                    self.write(" = {0}");
                                }
                                self.write(";\n");
                            }
                            crate::parser::TypeKind::Slice { element }
                            | crate::parser::TypeKind::ArrayRef { element, .. } => {
                                let elem_type = self.type_to_c(element);
                                self.write_indent();
                                self.write(&format!("{}* {}", elem_type, name.name));
                                if let Some(init) = init {
                                    self.write(" = ");
                                    self.generate_expr(init);
                                } else {
                                    self.write(" = NULL");
                                }
                                self.write(";\n");
                            }
                            crate::parser::TypeKind::MutRef(inner)
                            | crate::parser::TypeKind::Ref(inner) => {
                                let inner_type = self.type_to_c(inner);
                                self.write_indent();
                                self.write(&format!("{}* {}", inner_type, name.name));
                                if let Some(init) = init {
                                    self.write(" = ");
                                    self.generate_expr(init);
                                } else {
                                    self.write(" = NULL");
                                }
                                self.write(";\n");
                            }
                            _ => {
                                self.write_indent();
                                self.write(&format!("{} {}", base_type, name.name));
                                if let Some(init) = init {
                                    self.write(" = ");
                                    self.generate_expr(init);
                                } else {
                                    self.write(&format!(" = {}", self.default_value_for_type(ty)));
                                }
                                self.write(";\n");
                            }
                        }
                    }
                } else if let Some(init) = init {
                    // No type annotation - use auto (C23) or infer
                    // For C compatibility, try to infer the type from the init expression
                    self.write_indent();
                    let inferred_type = self.infer_expr_c_type(init);
                    self.write(&format!("{} {} = ", inferred_type, name.name));
                    self.generate_expr(init);
                    self.write(";\n");
                } else {
                    // No type, no init - use int as fallback
                    self.write_indent();
                    self.write(&format!("int {} = 0;\n", name.name));
                }
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
                        let native = p.to_native();
                        self.write_indent();

                        match native {
                            crate::parser::PrimitiveType::U16
                            | crate::parser::PrimitiveType::I16 => {
                                // Write 2 bytes
                                self.write("{ uint16_t __v = (uint16_t)(");
                                self.generate_expr(value);
                                self.write("); ");
                                if little_endian {
                                    self.generate_expr(array);
                                    self.write("[");
                                    self.generate_expr(start);
                                    self.write("] = (uint8_t)(__v & 0xFF); ");
                                    self.generate_expr(array);
                                    self.write("[");
                                    self.generate_expr(start);
                                    self.write(" + 1] = (uint8_t)(__v >> 8); }");
                                } else {
                                    self.generate_expr(array);
                                    self.write("[");
                                    self.generate_expr(start);
                                    self.write("] = (uint8_t)(__v >> 8); ");
                                    self.generate_expr(array);
                                    self.write("[");
                                    self.generate_expr(start);
                                    self.write(" + 1] = (uint8_t)(__v & 0xFF); }");
                                }
                            }
                            crate::parser::PrimitiveType::U32
                            | crate::parser::PrimitiveType::I32 => {
                                self.write("{ uint32_t __v = (uint32_t)(");
                                self.generate_expr(value);
                                self.write("); ");
                                if little_endian {
                                    for i in 0..4 {
                                        self.generate_expr(array);
                                        self.write("[");
                                        self.generate_expr(start);
                                        self.write(&format!(
                                            " + {}] = (uint8_t)(__v >> {}); ",
                                            i,
                                            i * 8
                                        ));
                                    }
                                } else {
                                    for i in 0..4 {
                                        self.generate_expr(array);
                                        self.write("[");
                                        self.generate_expr(start);
                                        self.write(&format!(
                                            " + {}] = (uint8_t)(__v >> {}); ",
                                            i,
                                            (3 - i) * 8
                                        ));
                                    }
                                }
                                self.write("}");
                            }
                            crate::parser::PrimitiveType::U64
                            | crate::parser::PrimitiveType::I64 => {
                                self.write("{ uint64_t __v = (uint64_t)(");
                                self.generate_expr(value);
                                self.write("); ");
                                if little_endian {
                                    for i in 0..8 {
                                        self.generate_expr(array);
                                        self.write("[");
                                        self.generate_expr(start);
                                        self.write(&format!(
                                            " + {}] = (uint8_t)(__v >> {}); ",
                                            i,
                                            i * 8
                                        ));
                                    }
                                } else {
                                    for i in 0..8 {
                                        self.generate_expr(array);
                                        self.write("[");
                                        self.generate_expr(start);
                                        self.write(&format!(
                                            " + {}] = (uint8_t)(__v >> {}); ",
                                            i,
                                            (7 - i) * 8
                                        ));
                                    }
                                }
                                self.write("}");
                            }
                            crate::parser::PrimitiveType::U128
                            | crate::parser::PrimitiveType::I128 => {
                                if little_endian {
                                    self.write("__write_u128le(");
                                } else {
                                    self.write("__write_u128be(");
                                }
                                self.generate_expr(array);
                                self.write(" + ");
                                self.generate_expr(start);
                                self.write(", (__uint128_t)(");
                                self.generate_expr(value);
                                self.write("))");
                            }
                            _ => {
                                // Fallback
                                self.generate_expr(target);
                                self.write(" = ");
                                self.generate_expr(value);
                            }
                        }
                        self.write("\n");
                        return;
                    }
                }

                // Check for slice assignment (memcpy)
                if let ExprKind::Slice {
                    array, start, end, ..
                } = &target.kind
                {
                    self.write_indent();
                    self.write("memcpy(");
                    self.generate_expr(array);
                    self.write(" + ");
                    self.generate_expr(start);
                    self.write(", ");
                    self.generate_expr(value);
                    self.write(", ");
                    self.generate_expr(end);
                    self.write(" - (");
                    self.generate_expr(start);
                    self.write("));\n");
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
                // Infer iterator type from bounds
                let iter_type = self.infer_expr_c_type(start);
                self.write_indent();
                self.write(&format!("for ({} {} = ", iter_type, var.name));
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
                self.writeln("while (1) {");
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
                if *n > u64::MAX as u128 {
                    // 128-bit literal
                    let hi = (*n >> 64) as u64;
                    let lo = *n as u64;
                    self.write(&format!(
                        "((__uint128_t){:#X}ULL << 64 | (__uint128_t){:#X}ULL)",
                        hi, lo
                    ));
                } else if *n > u32::MAX as u128 {
                    self.write(&format!("{}ULL", n));
                } else if *n > i32::MAX as u128 {
                    self.write(&format!("{}U", n));
                } else {
                    self.write(&format!("{}", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // String literal as C string bytes
                self.write(&format!("(uint8_t*)\"{}\"", escape_c_string(s)));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("(uint8_t*)\"{}\"", escape_c_string(s)));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to a C byte array literal
                let bytes: Vec<String> = h
                    .as_bytes()
                    .chunks(2)
                    .map(|pair| {
                        let hex_str = std::str::from_utf8(pair).unwrap_or("00");
                        format!("0x{}", hex_str)
                    })
                    .collect();
                self.write(&format!(
                    "(uint8_t[{}]){{{}}}",
                    bytes.len(),
                    bytes.join(", ")
                ));
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                // Check for array comparisons using constant_time_eq
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
                        self.write(", ");
                        // Try to determine length
                        self.generate_array_len(left, right);
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
            ExprKind::Slice { array, start, .. } => {
                // In C, slicing produces a pointer: array + start
                // But we often need length too; this just produces the pointer
                self.write("(");
                self.generate_expr(array);
                self.write(" + ");
                self.generate_expr(start);
                self.write(")");
            }
            ExprKind::Field { object, field } => {
                // Check if the object is a pointer (from &mut / & parameters) -> use ->
                if let ExprKind::Ident(ident) = &object.kind
                    && self.pointer_vars.contains(&ident.name)
                {
                    self.write(&format!("{}->{}", ident.name, field.name));
                    return;
                }
                self.generate_expr(object);
                self.write(&format!(".{}", field.name));
            }
            ExprKind::Call { func, args } => {
                // Handle Reader/Writer constructor calls
                if let ExprKind::Ident(ident) = &func.kind {
                    if ident.name == "Reader" {
                        self.write("Reader_new(");
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
                        self.write("Writer_new(");
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_expr(arg);
                        }
                        self.write(")");
                        return;
                    }

                    // Handle secure_zero calls on non-u8 arrays (e.g., uint32_t[8])
                    // secure_zero expects uint8_t* but state.h is uint32_t[8].
                    // Generate memset(state.h, 0, sizeof(state.h)) instead.
                    if ident.name == "secure_zero"
                        && args.len() == 1
                        && let ExprKind::MutRef(inner) = &args[0].kind
                        && self.is_non_u8_array_expr(inner)
                    {
                        self.write("memset(");
                        self.generate_expr(inner);
                        self.write(", 0, sizeof(");
                        self.generate_expr(inner);
                        self.write("))");
                        return;
                    }
                }

                // Check for method calls like slice.len(), reader.read_u32()
                if let ExprKind::Field { object, field } = &func.kind {
                    // .len() -> sizeof or stored length
                    if field.name == "len" && args.is_empty() {
                        // In C, we can use sizeof for fixed arrays, but for slices
                        // we'd need a separate length. For now, use sizeof/element size
                        self.write("sizeof(");
                        self.generate_expr(object);
                        self.write(")");
                        return;
                    }

                    // Handle reader.read(&mut struct)
                    if field.name == "read"
                        && args.len() == 1
                        && let ExprKind::MutRef(inner) = &args[0].kind
                        && let ExprKind::Ident(var_ident) = &inner.kind
                        && let Some(struct_name) = self.var_types.get(&var_ident.name).cloned()
                        && let Some(fields) = self.struct_defs.get(&struct_name).cloned()
                    {
                        let accessor = if self.pointer_vars.contains(&var_ident.name) {
                            "->"
                        } else {
                            "."
                        };
                        self.write("do { ");
                        for field_info in &fields {
                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty)
                            {
                                self.write(&format!(
                                    "{}{}{} = {}(&",
                                    var_ident.name, accessor, field_info.name, read_method
                                ));
                                self.generate_expr(object);
                                self.write("); ");
                            }
                        }
                        self.write("} while(0)");
                        return;
                    }

                    // Handle writer.write(&struct)
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
                            let accessor = if self.pointer_vars.contains(&var_ident.name) {
                                "->"
                            } else {
                                "."
                            };
                            self.write("do { ");
                            for field_info in &fields {
                                if let Some(write_method) =
                                    self.get_write_method_for_type(&field_info.ty)
                                {
                                    self.write(&format!("{}(&", write_method));
                                    self.generate_expr(object);
                                    self.write(&format!(
                                        ", {}{}{}); ",
                                        var_ident.name, accessor, field_info.name
                                    ));
                                }
                            }
                            self.write("} while(0)");
                            return;
                        }
                    }

                    // Reader/Writer method calls → C function calls
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
                        // Determine if it's a Reader or Writer method
                        let is_reader = field.name.starts_with("read_") || field.name == "eof";
                        let prefix = if is_reader { "Reader" } else { "Writer" };
                        self.write(&format!("{}_{}", prefix, field.name));
                        self.write("(&");
                        self.generate_expr(object);
                        for arg in args {
                            self.write(", ");
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
                        // Generate: StructName__method(&object, args...) or StructName__method(object, args...) if already a pointer
                        let is_ptr = self.pointer_vars.contains(&obj_ident.name);
                        let mangled_name = mangled_name.clone();
                        if is_ptr {
                            self.write(&format!("{}(", mangled_name));
                        } else {
                            self.write(&format!("{}(&", mangled_name));
                        }
                        self.generate_expr(object);
                        for arg in args {
                            self.write(", ");
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
                // Generate C array initializer
                self.write("{");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_expr(elem);
                }
                self.write("}");
            }
            ExprKind::ArrayRepeat { value, count: _ } => {
                // In C, we can't directly create repeated arrays inline.
                // For zero-fill, use {0}. Otherwise, need a loop or compound literal.
                if let ExprKind::Integer(0) = &value.kind {
                    self.write("{0}");
                } else {
                    // Use a compound literal with memset-like pattern
                    // This is a simplification - in practice, the generated code might need
                    // to be adjusted based on context
                    self.write("{0}");
                }
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) => {
                // Reference: take address in C
                // But for arrays, they already decay to pointers
                if is_array_like_expr(inner) {
                    self.generate_expr(inner);
                } else {
                    self.write("&");
                    self.generate_expr(inner);
                }
            }
            ExprKind::MutRef(inner) => {
                // Mutable reference: same as ref in C
                if is_array_like_expr(inner) {
                    self.generate_expr(inner);
                } else {
                    self.write("&");
                    self.generate_expr(inner);
                }
            }
            ExprKind::Deref(inner) => {
                self.write("*(");
                self.generate_expr(inner);
                self.write(")");
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
                // C struct literal (compound literal)
                self.write(&format!("(struct {}){{", name.name));
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
                // C ternary operator
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
                // Generate a compound literal for the enum
                if args.is_empty() {
                    self.write(&format!(
                        "({}){{ .tag = {}__{} }}",
                        enum_name.name, enum_name.name, variant_name.name
                    ));
                } else {
                    self.write(&format!(
                        "({}){{ .tag = {}__{}",
                        enum_name.name, enum_name.name, variant_name.name
                    ));
                    self.write(&format!(", .data.{} = {{ ", variant_name.name));
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.write(&format!(".v{} = ", i));
                        self.generate_expr(arg);
                    }
                    self.write(" } }");
                }
            }
            ExprKind::Match { expr, arms } => {
                // Generate match as a GCC statement expression
                // ({ Type __match = expr; Type __result; if (...) ... ; __result; })
                // Since we don't know the result type easily, use a lambda-like approach
                // with GCC statement expressions
                self.write("({ __typeof__(");
                // Try to get result type from first arm body
                self.generate_expr(&arms[0].body);
                self.write(") __result; ");
                // Evaluate scrutinee
                self.write("__typeof__(");
                self.generate_expr(expr);
                self.write(") __match = ");
                self.generate_expr(expr);
                self.write("; ");
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write(" else ");
                    }
                    self.generate_pattern_match(&arm.pattern, "__match");
                    self.write(" { __result = ");
                    self.generate_expr(&arm.body);
                    self.write("; }");
                }
                self.write(" __result; })");
            }
            ExprKind::MethodCall {
                receiver,
                mangled_name,
                args,
                ..
            } => {
                // Generate: mangled_name(&receiver, args...)
                self.write(&format!("{}(&", mangled_name));
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
                // Resolved by monomorphization
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
                // Resolved by monomorphization - generate as regular call
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
                self.write("if (1)");
            }
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("if ({} == ", scrutinee));
                self.generate_expr(lit_expr);
                self.write(")");
            }
            PatternKind::Ident(_ident) => {
                // Binding pattern - always matches
                self.write("if (1)");
            }
            PatternKind::EnumVariant {
                enum_name: _,
                variant_name,
                bindings: _,
            } => {
                // Check tag field
                self.write(&format!("if ({}.tag == {})", scrutinee, variant_name.name));
            }
            PatternKind::Tuple(_patterns) => {
                self.write("if (1)");
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
            PatternKind::Wildcard => self.write("1"),
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("{} == ", scrutinee));
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(_) => self.write("1"),
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!("{}.tag == {}", scrutinee, variant_name.name));
            }
            PatternKind::Tuple(_) => self.write("1"),
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
                self.write("algoc_assert(");
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
                let little_endian = endian == Endianness::Little;
                let native = p.to_native();

                // Check if source is a byte sequence (endian conversion from bytes)
                if is_byte_sequence_expr(expr) {
                    match native {
                        PrimitiveType::U16 | PrimitiveType::I16 => {
                            self.write("({ const uint8_t *__b = ");
                            self.generate_expr(expr);
                            if little_endian {
                                self.write("; (uint16_t)__b[0] | ((uint16_t)__b[1] << 8); })");
                            } else {
                                self.write("; ((uint16_t)__b[0] << 8) | (uint16_t)__b[1]; })");
                            }
                        }
                        PrimitiveType::U32 | PrimitiveType::I32 => {
                            self.write("({ const uint8_t *__b = ");
                            self.generate_expr(expr);
                            if little_endian {
                                self.write("; (uint32_t)__b[0] | ((uint32_t)__b[1] << 8) | ((uint32_t)__b[2] << 16) | ((uint32_t)__b[3] << 24); })");
                            } else {
                                self.write("; ((uint32_t)__b[0] << 24) | ((uint32_t)__b[1] << 16) | ((uint32_t)__b[2] << 8) | (uint32_t)__b[3]; })");
                            }
                        }
                        PrimitiveType::U64 | PrimitiveType::I64 => {
                            self.write("({ const uint8_t *__b = ");
                            self.generate_expr(expr);
                            if little_endian {
                                self.write("; (uint64_t)__b[0] | ((uint64_t)__b[1] << 8) | ((uint64_t)__b[2] << 16) | ((uint64_t)__b[3] << 24) | ((uint64_t)__b[4] << 32) | ((uint64_t)__b[5] << 40) | ((uint64_t)__b[6] << 48) | ((uint64_t)__b[7] << 56); })");
                            } else {
                                self.write("; ((uint64_t)__b[0] << 56) | ((uint64_t)__b[1] << 48) | ((uint64_t)__b[2] << 40) | ((uint64_t)__b[3] << 32) | ((uint64_t)__b[4] << 24) | ((uint64_t)__b[5] << 16) | ((uint64_t)__b[6] << 8) | (uint64_t)__b[7]; })");
                            }
                        }
                        PrimitiveType::U128 | PrimitiveType::I128 => {
                            if little_endian {
                                self.write("__read_u128le(");
                            } else {
                                self.write("__read_u128be(");
                            }
                            self.generate_expr(expr);
                            self.write(")");
                        }
                        _ => {
                            // Fallback: simple cast
                            let c_type = self.type_to_c(ty);
                            self.write(&format!("({})(", c_type));
                            self.generate_expr(expr);
                            self.write(")");
                        }
                    }
                    return;
                }

                // Integer to integer with endianness specification - just mask/cast
                let c_type = self.type_to_c(ty);
                self.write(&format!("({})(", c_type));
                self.generate_expr(expr);
                self.write(")");
                return;
            }
        }

        // Check for integer to byte array cast
        if let TypeKind::Array { element, size } = &ty.kind
            && let TypeKind::Primitive(PrimitiveType::U8) = &element.kind
        {
            let (little_endian, bits) = self.get_expr_endianness_info(expr);

            match bits {
                16 => {
                    self.write("({ uint16_t __v = (uint16_t)(");
                    // Unwrap one layer of cast to get the raw value
                    if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                        self.generate_expr(inner);
                    } else {
                        self.generate_expr(expr);
                    }
                    self.write(&format!("); uint8_t __a[{}]; ", size));
                    if little_endian {
                        self.write(
                            "__a[0] = (uint8_t)(__v & 0xFF); __a[1] = (uint8_t)(__v >> 8); ",
                        );
                    } else {
                        self.write(
                            "__a[0] = (uint8_t)(__v >> 8); __a[1] = (uint8_t)(__v & 0xFF); ",
                        );
                    }
                    // We can't return a local array. Use memcpy pattern or compound literal.
                    // This is a limitation of C. Use a statement expression with memcpy.
                    self.write("memcpy(__a, __a, 0); __a; })");
                }
                64 => {
                    self.write("({ uint64_t __v = (uint64_t)(");
                    if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                        self.generate_expr(inner);
                    } else {
                        self.generate_expr(expr);
                    }
                    self.write(&format!("); uint8_t __a[{}]; ", size));
                    if little_endian {
                        for i in 0..8 {
                            self.write(&format!("__a[{}] = (uint8_t)(__v >> {}); ", i, i * 8));
                        }
                    } else {
                        for i in 0..8 {
                            self.write(&format!(
                                "__a[{}] = (uint8_t)(__v >> {}); ",
                                i,
                                (7 - i) * 8
                            ));
                        }
                    }
                    self.write("__a; })");
                }
                128 => {
                    self.write("({ __uint128_t __v = (__uint128_t)(");
                    if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                        self.generate_expr(inner);
                    } else {
                        self.generate_expr(expr);
                    }
                    self.write("); uint8_t __a[16]; ");
                    if little_endian {
                        self.write("__write_u128le(__a, __v); ");
                    } else {
                        self.write("__write_u128be(__a, __v); ");
                    }
                    self.write("__a; })");
                }
                _ => {
                    // 32-bit
                    self.write("({ uint32_t __v = (uint32_t)(");
                    if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                        self.generate_expr(inner);
                    } else {
                        self.generate_expr(expr);
                    }
                    self.write(&format!("); uint8_t __a[{}]; ", size));
                    if little_endian {
                        for i in 0..4 {
                            self.write(&format!("__a[{}] = (uint8_t)(__v >> {}); ", i, i * 8));
                        }
                    } else {
                        for i in 0..4 {
                            self.write(&format!(
                                "__a[{}] = (uint8_t)(__v >> {}); ",
                                i,
                                (3 - i) * 8
                            ));
                        }
                    }
                    self.write("__a; })");
                }
            }
            return;
        }

        // Standard C cast
        match &ty.kind {
            TypeKind::Primitive(_) => {
                let c_type = self.type_to_c(ty);
                self.write(&format!("({})(", c_type));
                self.generate_expr(expr);
                self.write(")");
            }
            TypeKind::Named(ident) => {
                self.write(&format!("(struct {})(", ident.name));
                self.generate_expr(expr);
                self.write(")");
            }
            _ => {
                let c_type = self.type_to_c(ty);
                self.write(&format!("({})(", c_type));
                self.generate_expr(expr);
                self.write(")");
            }
        }
    }

    /// Try to determine the length of an array-like expression for comparisons
    fn generate_array_len(&mut self, left: &Expr, right: &Expr) {
        // Try to get length from hex literals
        if let ExprKind::Hex(h) = &left.kind {
            self.write(&format!("{}", h.len() / 2));
            return;
        }
        if let ExprKind::Hex(h) = &right.kind {
            self.write(&format!("{}", h.len() / 2));
            return;
        }
        // Try from array literal
        if let ExprKind::Array(elems) = &left.kind {
            self.write(&format!("{}", elems.len()));
            return;
        }
        if let ExprKind::Array(elems) = &right.kind {
            self.write(&format!("{}", elems.len()));
            return;
        }
        // Try from string/bytes
        if let ExprKind::String(s) = &left.kind {
            self.write(&format!("{}", s.len()));
            return;
        }
        if let ExprKind::Bytes(s) = &left.kind {
            self.write(&format!("{}", s.len()));
            return;
        }
        if let ExprKind::String(s) = &right.kind {
            self.write(&format!("{}", s.len()));
            return;
        }
        if let ExprKind::Bytes(s) = &right.kind {
            self.write(&format!("{}", s.len()));
            return;
        }
        // Try from slice
        if let ExprKind::Slice { start, end, .. } = &left.kind {
            self.write("(");
            self.generate_expr(end);
            self.write(" - ");
            self.generate_expr(start);
            self.write(")");
            return;
        }
        if let ExprKind::Slice { start, end, .. } = &right.kind {
            self.write("(");
            self.generate_expr(end);
            self.write(" - ");
            self.generate_expr(start);
            self.write(")");
            return;
        }
        // Fallback: use sizeof on the left operand
        self.write("sizeof(");
        self.generate_expr(left);
        self.write(")");
    }

    /// Get the Reader C function name for reading a field type
    fn get_read_method_for_type(&self, ty: &ParserType) -> Option<String> {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        match &ty.kind {
            TypeKind::Primitive(p) => {
                let endian = p.endianness();
                let native = p.to_native();
                let suffix = match endian {
                    Endianness::Big => "be",
                    Endianness::Little => "le",
                    Endianness::Native => "be",
                };
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => Some("Reader_read_u8".to_string()),
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        Some(format!("Reader_read_u16{}", suffix))
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        Some(format!("Reader_read_u32{}", suffix))
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        Some(format!("Reader_read_u64{}", suffix))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Get the Writer C function name for writing a field type
    fn get_write_method_for_type(&self, ty: &ParserType) -> Option<String> {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        match &ty.kind {
            TypeKind::Primitive(p) => {
                let endian = p.endianness();
                let native = p.to_native();
                let suffix = match endian {
                    Endianness::Big => "be",
                    Endianness::Little => "le",
                    Endianness::Native => "be",
                };
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => Some("Writer_write_u8".to_string()),
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        Some(format!("Writer_write_u16{}", suffix))
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        Some(format!("Writer_write_u32{}", suffix))
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        Some(format!("Writer_write_u64{}", suffix))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Infer a C type from an expression (best-effort)
    fn infer_expr_c_type(&self, expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Integer(n) => {
                if *n > u64::MAX as u128 {
                    "__uint128_t".to_string()
                } else if *n > u32::MAX as u128 {
                    "uint64_t".to_string()
                } else {
                    "uint32_t".to_string()
                }
            }
            ExprKind::Bool(_) => "bool".to_string(),
            ExprKind::String(_) | ExprKind::Bytes(_) | ExprKind::Hex(_) => "uint8_t*".to_string(),
            ExprKind::Cast { ty, .. } => self.type_to_c(ty),
            ExprKind::Call { func, .. } => {
                // Try to infer from known constructor patterns
                if let ExprKind::Ident(ident) = &func.kind
                    && ident.name.ends_with("__new")
                {
                    let struct_name = &ident.name[..ident.name.len() - 5];
                    return format!("struct {}", struct_name);
                }
                "uint32_t".to_string()
            }
            ExprKind::TypeStaticCall {
                type_name,
                method_name,
                ..
            } => {
                if method_name.name == "new" {
                    return format!("struct {}", type_name.name);
                }
                "uint32_t".to_string()
            }
            ExprKind::StructLit { name, .. } => {
                format!("struct {}", name.name)
            }
            ExprKind::Array(_) | ExprKind::ArrayRepeat { .. } => "uint8_t*".to_string(),
            ExprKind::Binary { left, .. } => self.infer_expr_c_type(left),
            ExprKind::Paren(inner) => self.infer_expr_c_type(inner),
            _ => "uint32_t".to_string(),
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
        // Default to big endian (network byte order), 32 bits
        (false, 32)
    }

    /// Check if an expression refers to a non-u8 array (e.g., state.h where h: [u32; 8]).
    /// Used to detect secure_zero calls on non-u8 arrays that need special handling.
    fn is_non_u8_array_expr(&self, expr: &Expr) -> bool {
        use crate::parser::TypeKind;
        if let ExprKind::Field { object, field } = &expr.kind
            && let ExprKind::Ident(obj_ident) = &object.kind
            && let Some(struct_name) = self.var_types.get(&obj_ident.name)
            && let Some(fields) = self.struct_defs.get(struct_name)
        {
            for f in fields {
                if f.name == field.name
                    && let TypeKind::Array { element, .. } = &f.ty.kind
                {
                    if let TypeKind::Primitive(p) = &element.kind {
                        return *p != crate::parser::PrimitiveType::U8;
                    }
                    return true;
                }
            }
        }
        false
    }
}

impl Default for ObjCGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for ObjCGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();

        // Pre-pass: collect struct definitions and method info
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

        // Header
        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("// Compile with: clang -O2 -framework Foundation -lobjc -o output file.m");
        self.writeln("");
        self.writeln("#import <Foundation/Foundation.h>");
        self.writeln("#include <stdint.h>");
        self.writeln("#include <stdbool.h>");
        self.writeln("#include <string.h>");
        self.writeln("#include <stdio.h>");
        self.writeln("#include <stdlib.h>");
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

        // Generate test runner as main()
        if self.include_tests {
            self.writeln("// Test Runner");
            self.writeln("int main(int argc, char *argv[]) {");
            self.indent();
            self.writeln("@autoreleasepool {");
            self.indent();
            self.writeln("int __passed = 0;");
            self.writeln("int __failed = 0;");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("__test_name = \"{}\";", name));
                self.writeln("__test_failures = 0;");
                self.writeln(&format!("test_{}();", name));
                self.writeln("if (__test_failures == 0) {");
                self.indent();
                self.writeln(&format!("printf(\"PASS: {}\\n\");", name));
                self.writeln("__passed++;");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("printf(\"FAIL: {}\\n\");", name));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("printf(\"\\n%d passed, %d failed\\n\", __passed, __failed);");
            self.writeln("return __failed == 0 ? 0 : 1;");
            self.dedent();
            self.writeln("}");
            self.dedent();
            self.writeln("}");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "m"
    }

    fn language_name(&self) -> &'static str {
        "Objective-C"
    }
}

/// Escape a string for C string literals
fn escape_c_string(s: &str) -> String {
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
