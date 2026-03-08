//! C code generator
//!
//! Generates C11 code from the analyzed AST.
//! Uses stdint.h types for fixed-width integers and stack-allocated arrays where possible.
//! Slices are represented as pointer + length pairs.

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

/// Info about a function parameter for C code generation
#[derive(Clone)]
struct FuncParamInfo {
    needs_len: bool,
}

/// C code generator
pub struct CGenerator {
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
    /// Function signatures: func_name -> list of param info (for generating correct call args)
    func_signatures: HashMap<String, Vec<FuncParamInfo>>,
    /// Variables that are slices/arrays (need _len companion when passed to functions)
    slice_vars: HashSet<String>,
    /// Variables that are fixed-size arrays (decay to pointers, no & needed)
    /// Maps variable name to known array size.
    fixed_array_vars: HashMap<String, u64>,
    /// Generated `_len` companion parameter names (e.g., "data_len" from param `data: &[u8]`).
    /// Used to detect local variable name conflicts.
    len_param_names: HashSet<String>,
    /// Mapping from original variable name to renamed variable (to avoid _len conflicts).
    var_renames: HashMap<String, String>,
}

impl CGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            pointer_vars: HashSet::new(),
            func_signatures: HashMap::new(),
            slice_vars: HashSet::new(),
            fixed_array_vars: HashMap::new(),
            len_param_names: HashSet::new(),
            var_renames: HashMap::new(),
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

    /// Map a parser type to its C type string
    fn type_to_c(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;

        match &ty.kind {
            TypeKind::Primitive(p) => self.primitive_to_c(*p).to_string(),
            TypeKind::Array { element, size } => {
                // Arrays are handled specially at declaration sites
                // Return the element type here
                format!("{}[{}]", self.type_to_c(element), size)
            }
            TypeKind::Slice { element } => {
                // Slices are pointer + length, represented as just pointer type
                format!("{}*", self.type_to_c(element))
            }
            TypeKind::ArrayRef { element, .. } => {
                // Reference to fixed array = pointer
                format!("{}*", self.type_to_c(element))
            }
            TypeKind::MutRef(inner) => {
                match &inner.kind {
                    TypeKind::Slice { element } => {
                        // &mut [T] -> T* (pointer)
                        format!("{}*", self.type_to_c(element))
                    }
                    TypeKind::Array { element, .. } => {
                        format!("{}*", self.type_to_c(element))
                    }
                    _ => {
                        format!("{}*", self.type_to_c(inner))
                    }
                }
            }
            TypeKind::Ref(inner) => match &inner.kind {
                TypeKind::Slice { element } => {
                    format!("const {}*", self.type_to_c(element))
                }
                TypeKind::Array { element, .. } => {
                    format!("const {}*", self.type_to_c(element))
                }
                _ => {
                    format!("const {}*", self.type_to_c(inner))
                }
            },
            TypeKind::Named(ident) => {
                format!("struct {}", ident.name)
            }
            TypeKind::SelfType => "void*".to_string(),
        }
    }

    /// Map a primitive type to C type name
    fn primitive_to_c(&self, p: crate::parser::PrimitiveType) -> &'static str {
        use crate::parser::PrimitiveType;
        let native = p.to_native();
        match native {
            PrimitiveType::U8 => "uint8_t",
            PrimitiveType::U16 => "uint16_t",
            PrimitiveType::U32 => "uint32_t",
            PrimitiveType::U64 => "uint64_t",
            PrimitiveType::U128 => "__uint128_t",
            PrimitiveType::I8 => "int8_t",
            PrimitiveType::I16 => "int16_t",
            PrimitiveType::I32 => "int32_t",
            PrimitiveType::I64 => "int64_t",
            PrimitiveType::I128 => "__int128_t",
            PrimitiveType::Bool => "bool",
            _ => "uint32_t", // Shouldn't reach here after to_native()
        }
    }

    /// Get the base C type for a parser type (without array dimensions)
    fn type_to_c_base(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Array { element, .. } => self.type_to_c_base(element),
            _ => self.type_to_c(ty),
        }
    }

    /// Check if a parameter type requires a companion _len argument in C.
    /// Only dynamically-sized types (slices, array refs) need _len.
    /// Fixed-size arrays (TypeKind::Array) do NOT need _len since the size is known at compile time.
    fn param_needs_len(ty: &ParserType) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Slice { .. } => true,
            TypeKind::ArrayRef { .. } => true,
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                matches!(inner.kind, TypeKind::Slice { .. })
            }
            _ => false,
        }
    }

    /// Check if a struct field type is a slice-like type that needs a companion _len field
    fn is_slice_field_type(ty: &ParserType) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Slice { .. } => true,
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                matches!(inner.kind, TypeKind::Slice { .. })
            }
            _ => false,
        }
    }

    /// Check if a type is an array type
    fn is_array_type(ty: &ParserType) -> bool {
        matches!(ty.kind, crate::parser::TypeKind::Array { .. })
    }

    /// Get array size from a type if it's an array
    fn get_array_size(ty: &ParserType) -> Option<u64> {
        if let crate::parser::TypeKind::Array { size, .. } = &ty.kind {
            Some(*size)
        } else {
            None
        }
    }

    /// Look up a struct field's fixed array size (element count).
    /// Returns Some(size) if the field is a fixed-size array, None otherwise.
    fn get_struct_field_array_size(&self, object: &Expr, field_name: &str) -> Option<u64> {
        // Determine the struct type from var_types
        let struct_name = if let ExprKind::Ident(ident) = &object.kind {
            self.var_types.get(&ident.name)?.clone()
        } else {
            return None;
        };
        // Look up the field in struct_defs
        let fields = self.struct_defs.get(&struct_name)?;
        let field_info = fields.iter().find(|f| f.name == field_name)?;
        Self::get_array_size(&field_info.ty)
    }

    /// Get byte size for a primitive type
    fn primitive_byte_size(prim: &crate::parser::PrimitiveType) -> u64 {
        use crate::parser::PrimitiveType;
        match prim {
            PrimitiveType::U8 | PrimitiveType::I8 | PrimitiveType::Bool => 1,
            PrimitiveType::U16
            | PrimitiveType::I16
            | PrimitiveType::U16Be
            | PrimitiveType::I16Be
            | PrimitiveType::U16Le
            | PrimitiveType::I16Le => 2,
            PrimitiveType::U32
            | PrimitiveType::I32
            | PrimitiveType::U32Be
            | PrimitiveType::I32Be
            | PrimitiveType::U32Le
            | PrimitiveType::I32Le => 4,
            PrimitiveType::U64
            | PrimitiveType::I64
            | PrimitiveType::U64Be
            | PrimitiveType::I64Be
            | PrimitiveType::U64Le
            | PrimitiveType::I64Le => 8,
            PrimitiveType::U128
            | PrimitiveType::I128
            | PrimitiveType::U128Be
            | PrimitiveType::I128Be
            | PrimitiveType::U128Le
            | PrimitiveType::I128Le => 16,
        }
    }

    /// Look up a struct field's total byte count (element_count * element_byte_size).
    /// Returns Some(bytes) if the field is a fixed-size array, None otherwise.
    fn get_struct_field_byte_count(&self, object: &Expr, field_name: &str) -> Option<u64> {
        use crate::parser::TypeKind;
        let struct_name = if let ExprKind::Ident(ident) = &object.kind {
            self.var_types.get(&ident.name)?.clone()
        } else {
            return None;
        };
        let fields = self.struct_defs.get(&struct_name)?;
        let field_info = fields.iter().find(|f| f.name == field_name)?;
        if let TypeKind::Array { element, size } = &field_info.ty.kind {
            if let TypeKind::Primitive(prim) = &element.kind {
                Some(size * Self::primitive_byte_size(prim))
            } else {
                Some(*size)
            }
        } else {
            None
        }
    }

    /// Get the return type string for a function
    fn return_type_to_c(&self, ty: Option<&ParserType>) -> String {
        self.return_type_to_c_with_self(ty, None)
    }

    /// Get the return type string for a function, resolving Self to the given struct name
    fn return_type_to_c_with_self(
        &self,
        ty: Option<&ParserType>,
        self_struct: Option<&str>,
    ) -> String {
        match ty {
            None => "void".to_string(),
            Some(ty) => {
                if Self::is_array_type(ty) {
                    // Can't return arrays in C, return void (use out param)
                    "void".to_string()
                } else {
                    // Resolve Self/SelfType to the actual struct name
                    match &ty.kind {
                        crate::parser::TypeKind::SelfType => {
                            if let Some(name) = self_struct {
                                name.to_string()
                            } else {
                                self.type_to_c(ty)
                            }
                        }
                        crate::parser::TypeKind::Named(ident) if ident.name == "Self" => {
                            if let Some(name) = self_struct {
                                name.to_string()
                            } else {
                                self.type_to_c(ty)
                            }
                        }
                        _ => self.type_to_c(ty),
                    }
                }
            }
        }
    }

    /// Default value expression for a C type
    fn default_value_for_type(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => {
                if matches!(p.to_native(), crate::parser::PrimitiveType::Bool) {
                    "false".to_string()
                } else {
                    "0".to_string()
                }
            }
            TypeKind::Named(_) => "{0}".to_string(),
            _ => "0".to_string(),
        }
    }

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        // Includes
        self.writeln("#include <stdint.h>");
        self.writeln("#include <stdbool.h>");
        self.writeln("#include <string.h>");
        self.writeln("#include <stdlib.h>");
        self.writeln("#include <stdio.h>");
        self.writeln("");

        // Endian conversion helpers
        self.writeln("// Endian conversion helpers");

        // 16-bit
        self.writeln("static inline uint16_t __algoc_bswap16(uint16_t v) {");
        self.indent();
        self.writeln("return (uint16_t)((v >> 8) | (v << 8));");
        self.dedent();
        self.writeln("}");

        // 32-bit
        self.writeln("static inline uint32_t __algoc_bswap32(uint32_t v) {");
        self.indent();
        self.writeln("return ((v >> 24) & 0xFF) | ((v >> 8) & 0xFF00) | ((v << 8) & 0xFF0000) | ((v << 24) & 0xFF000000u);");
        self.dedent();
        self.writeln("}");

        // 64-bit
        self.writeln("static inline uint64_t __algoc_bswap64(uint64_t v) {");
        self.indent();
        self.writeln(
            "v = ((v & 0x00000000FFFFFFFFULL) << 32) | ((v & 0xFFFFFFFF00000000ULL) >> 32);",
        );
        self.writeln(
            "v = ((v & 0x0000FFFF0000FFFFULL) << 16) | ((v & 0xFFFF0000FFFF0000ULL) >> 16);",
        );
        self.writeln(
            "v = ((v & 0x00FF00FF00FF00FFULL) << 8)  | ((v & 0xFF00FF00FF00FF00ULL) >> 8);",
        );
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");

        // 128-bit swap
        self.writeln("static inline __uint128_t __algoc_bswap128(__uint128_t v) {");
        self.indent();
        self.writeln("uint64_t hi = __algoc_bswap64((uint64_t)(v >> 64));");
        self.writeln("uint64_t lo = __algoc_bswap64((uint64_t)v);");
        self.writeln("return ((__uint128_t)lo << 64) | hi;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Read bytes as big-endian integers
        self.writeln("static inline uint16_t __algoc_read_u16be(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint16_t)((uint16_t)p[0] << 8 | (uint16_t)p[1]);");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline uint16_t __algoc_read_u16le(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint16_t)((uint16_t)p[1] << 8 | (uint16_t)p[0]);");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline uint32_t __algoc_read_u32be(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint32_t)p[0] << 24 | (uint32_t)p[1] << 16 | (uint32_t)p[2] << 8 | (uint32_t)p[3];");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline uint32_t __algoc_read_u32le(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint32_t)p[3] << 24 | (uint32_t)p[2] << 16 | (uint32_t)p[1] << 8 | (uint32_t)p[0];");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline uint64_t __algoc_read_u64be(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint64_t)p[0] << 56 | (uint64_t)p[1] << 48 | (uint64_t)p[2] << 40 | (uint64_t)p[3] << 32 | (uint64_t)p[4] << 24 | (uint64_t)p[5] << 16 | (uint64_t)p[6] << 8 | (uint64_t)p[7];");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline uint64_t __algoc_read_u64le(const uint8_t* p) {");
        self.indent();
        self.writeln("return (uint64_t)p[7] << 56 | (uint64_t)p[6] << 48 | (uint64_t)p[5] << 40 | (uint64_t)p[4] << 32 | (uint64_t)p[3] << 24 | (uint64_t)p[2] << 16 | (uint64_t)p[1] << 8 | (uint64_t)p[0];");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline __uint128_t __algoc_read_u128be(const uint8_t* p) {");
        self.indent();
        self.writeln(
            "return ((__uint128_t)__algoc_read_u64be(p) << 64) | __algoc_read_u64be(p + 8);",
        );
        self.dedent();
        self.writeln("}");

        self.writeln("static inline __uint128_t __algoc_read_u128le(const uint8_t* p) {");
        self.indent();
        self.writeln(
            "return ((__uint128_t)__algoc_read_u64le(p + 8) << 64) | __algoc_read_u64le(p);",
        );
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Write integers as bytes
        self.writeln("static inline void __algoc_write_u16be(uint8_t* p, uint16_t v) {");
        self.indent();
        self.writeln("p[0] = (uint8_t)(v >> 8); p[1] = (uint8_t)v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline void __algoc_write_u16le(uint8_t* p, uint16_t v) {");
        self.indent();
        self.writeln("p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8);");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline void __algoc_write_u32be(uint8_t* p, uint32_t v) {");
        self.indent();
        self.writeln("p[0] = (uint8_t)(v >> 24); p[1] = (uint8_t)(v >> 16); p[2] = (uint8_t)(v >> 8); p[3] = (uint8_t)v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline void __algoc_write_u32le(uint8_t* p, uint32_t v) {");
        self.indent();
        self.writeln("p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8); p[2] = (uint8_t)(v >> 16); p[3] = (uint8_t)(v >> 24);");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline void __algoc_write_u64be(uint8_t* p, uint64_t v) {");
        self.indent();
        self.writeln("p[0] = (uint8_t)(v >> 56); p[1] = (uint8_t)(v >> 48); p[2] = (uint8_t)(v >> 40); p[3] = (uint8_t)(v >> 32);");
        self.writeln("p[4] = (uint8_t)(v >> 24); p[5] = (uint8_t)(v >> 16); p[6] = (uint8_t)(v >> 8); p[7] = (uint8_t)v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline void __algoc_write_u64le(uint8_t* p, uint64_t v) {");
        self.indent();
        self.writeln("p[0] = (uint8_t)v; p[1] = (uint8_t)(v >> 8); p[2] = (uint8_t)(v >> 16); p[3] = (uint8_t)(v >> 24);");
        self.writeln("p[4] = (uint8_t)(v >> 32); p[5] = (uint8_t)(v >> 40); p[6] = (uint8_t)(v >> 48); p[7] = (uint8_t)(v >> 56);");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline void __algoc_write_u128be(uint8_t* p, __uint128_t v) {");
        self.indent();
        self.writeln("__algoc_write_u64be(p, (uint64_t)(v >> 64));");
        self.writeln("__algoc_write_u64be(p + 8, (uint64_t)v);");
        self.dedent();
        self.writeln("}");

        self.writeln("static inline void __algoc_write_u128le(uint8_t* p, __uint128_t v) {");
        self.indent();
        self.writeln("__algoc_write_u64le(p, (uint64_t)v);");
        self.writeln("__algoc_write_u64le(p + 8, (uint64_t)(v >> 64));");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Reader struct
        self.writeln("// Reader: streaming byte input");
        self.writeln("typedef struct {");
        self.indent();
        self.writeln("const uint8_t* data;");
        self.writeln("size_t len;");
        self.writeln("size_t pos;");
        self.dedent();
        self.writeln("} Reader;");
        self.writeln("");

        self.writeln("static Reader Reader_new(const uint8_t* data, size_t len) {");
        self.indent();
        self.writeln("Reader r; r.data = data; r.len = len; r.pos = 0; return r;");
        self.dedent();
        self.writeln("}");

        self.writeln("static uint8_t Reader_read_u8(Reader* r) {");
        self.indent();
        self.writeln("return r->data[r->pos++];");
        self.dedent();
        self.writeln("}");

        self.writeln("static uint16_t Reader_read_u16be(Reader* r) {");
        self.indent();
        self.writeln("uint16_t v = __algoc_read_u16be(r->data + r->pos); r->pos += 2; return v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static uint16_t Reader_read_u16le(Reader* r) {");
        self.indent();
        self.writeln("uint16_t v = __algoc_read_u16le(r->data + r->pos); r->pos += 2; return v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static uint16_t Reader_read_u16(Reader* r) { return Reader_read_u16be(r); }");

        self.writeln("static uint32_t Reader_read_u32be(Reader* r) {");
        self.indent();
        self.writeln("uint32_t v = __algoc_read_u32be(r->data + r->pos); r->pos += 4; return v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static uint32_t Reader_read_u32le(Reader* r) {");
        self.indent();
        self.writeln("uint32_t v = __algoc_read_u32le(r->data + r->pos); r->pos += 4; return v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static uint32_t Reader_read_u32(Reader* r) { return Reader_read_u32be(r); }");

        self.writeln("static uint64_t Reader_read_u64be(Reader* r) {");
        self.indent();
        self.writeln("uint64_t v = __algoc_read_u64be(r->data + r->pos); r->pos += 8; return v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static uint64_t Reader_read_u64le(Reader* r) {");
        self.indent();
        self.writeln("uint64_t v = __algoc_read_u64le(r->data + r->pos); r->pos += 8; return v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static uint64_t Reader_read_u64(Reader* r) { return Reader_read_u64be(r); }");

        self.writeln("static const uint8_t* Reader_read_bytes(Reader* r, size_t count) {");
        self.indent();
        self.writeln("const uint8_t* p = r->data + r->pos; r->pos += count; return p;");
        self.dedent();
        self.writeln("}");

        self.writeln("static const uint8_t* Reader_read_chunk(Reader* r, size_t max_size, size_t* out_len) {");
        self.indent();
        self.writeln("size_t remaining = r->len - r->pos;");
        self.writeln("size_t count = max_size < remaining ? max_size : remaining;");
        self.writeln("const uint8_t* p = r->data + r->pos;");
        self.writeln("r->pos += count;");
        self.writeln("*out_len = count;");
        self.writeln("return p;");
        self.dedent();
        self.writeln("}");

        self.writeln("static bool Reader_eof(const Reader* r) { return r->pos >= r->len; }");
        self.writeln("");

        // Writer struct
        self.writeln("// Writer: streaming byte output");
        self.writeln("typedef struct {");
        self.indent();
        self.writeln("uint8_t* data;");
        self.writeln("size_t len;");
        self.writeln("size_t pos;");
        self.dedent();
        self.writeln("} Writer;");
        self.writeln("");

        self.writeln("static Writer Writer_new(uint8_t* data, size_t len) {");
        self.indent();
        self.writeln("Writer w; w.data = data; w.len = len; w.pos = 0; return w;");
        self.dedent();
        self.writeln("}");

        self.writeln("static void Writer_write_u8(Writer* w, uint8_t v) {");
        self.indent();
        self.writeln("w->data[w->pos++] = v;");
        self.dedent();
        self.writeln("}");

        self.writeln("static void Writer_write_u16be(Writer* w, uint16_t v) {");
        self.indent();
        self.writeln("__algoc_write_u16be(w->data + w->pos, v); w->pos += 2;");
        self.dedent();
        self.writeln("}");

        self.writeln("static void Writer_write_u16le(Writer* w, uint16_t v) {");
        self.indent();
        self.writeln("__algoc_write_u16le(w->data + w->pos, v); w->pos += 2;");
        self.dedent();
        self.writeln("}");

        self.writeln(
            "static void Writer_write_u16(Writer* w, uint16_t v) { Writer_write_u16be(w, v); }",
        );

        self.writeln("static void Writer_write_u32be(Writer* w, uint32_t v) {");
        self.indent();
        self.writeln("__algoc_write_u32be(w->data + w->pos, v); w->pos += 4;");
        self.dedent();
        self.writeln("}");

        self.writeln("static void Writer_write_u32le(Writer* w, uint32_t v) {");
        self.indent();
        self.writeln("__algoc_write_u32le(w->data + w->pos, v); w->pos += 4;");
        self.dedent();
        self.writeln("}");

        self.writeln(
            "static void Writer_write_u32(Writer* w, uint32_t v) { Writer_write_u32be(w, v); }",
        );

        self.writeln("static void Writer_write_u64be(Writer* w, uint64_t v) {");
        self.indent();
        self.writeln("__algoc_write_u64be(w->data + w->pos, v); w->pos += 8;");
        self.dedent();
        self.writeln("}");

        self.writeln("static void Writer_write_u64le(Writer* w, uint64_t v) {");
        self.indent();
        self.writeln("__algoc_write_u64le(w->data + w->pos, v); w->pos += 8;");
        self.dedent();
        self.writeln("}");

        self.writeln(
            "static void Writer_write_u64(Writer* w, uint64_t v) { Writer_write_u64be(w, v); }",
        );

        self.writeln(
            "static void Writer_write_bytes(Writer* w, const uint8_t* data, size_t len) {",
        );
        self.indent();
        self.writeln("memcpy(w->data + w->pos, data, len); w->pos += len;");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Generate test runtime helpers (only when include_tests is true)
    fn generate_test_runtime(&mut self) {
        self.writeln("// Test Helpers");
        self.writeln("static int __test_failures = 0;");
        self.writeln("static const char* __test_name = \"\";");
        self.writeln("");

        self.writeln("static void __algoc_assert(bool condition) {");
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
        // This ensures monomorphized functions (appended at end) can be called
        // by functions defined earlier in the file.
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

    /// Generate forward declarations for all functions and methods.
    /// This allows functions to reference each other regardless of definition order,
    /// which is especially important for monomorphized functions that are appended
    /// at the end of the AST but called by functions defined earlier.
    fn generate_forward_declarations(&mut self, ast: &Ast) {
        let mut has_decls = false;

        for item in &ast.items {
            match &item.kind {
                ItemKind::Function(func) => {
                    self.generate_forward_decl(func);
                    has_decls = true;
                }
                ItemKind::Impl(impl_def) => {
                    for method in &impl_def.methods {
                        self.generate_method_forward_decl(&impl_def.target.name, method);
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

    /// Generate a forward declaration for a standalone function
    fn generate_forward_decl(&mut self, func: &Function) {
        let ret_ty = self.return_type_to_c(func.return_type.as_ref());
        self.write_indent();
        self.write(&format!("static {} {}(", ret_ty, func.name.name));

        let mut first = true;
        for param in &func.params {
            if !first {
                self.write(", ");
            }
            first = false;
            self.generate_param_decl(param);
        }

        if first {
            self.write("void");
        }

        self.write(");\n");
    }

    /// Generate a forward declaration for a method (mangled name)
    fn generate_method_forward_decl(&mut self, struct_name: &str, func: &Function) {
        let mangled_name = format!("{}__{}", struct_name, func.name.name);
        let ret_ty = self.return_type_to_c_with_self(func.return_type.as_ref(), Some(struct_name));
        self.write_indent();
        self.write(&format!("static {} {}(", ret_ty, mangled_name));

        let mut first = true;
        for param in &func.params {
            if !first {
                self.write(", ");
            }
            first = false;

            if param.name.name == "self" {
                self.write(&format!("{}* self", struct_name));
            } else {
                self.generate_param_decl(param);
            }
        }

        if first {
            self.write("void");
        }

        self.write(");\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        self.writeln(&format!("typedef struct {} {{", s.name.name));
        self.indent();
        for field in &s.fields {
            let base_ty = self.type_to_c_base(&field.ty);
            if Self::is_array_type(&field.ty) {
                if let Some(size) = Self::get_array_size(&field.ty) {
                    self.writeln(&format!("{} {}[{}];", base_ty, field.name.name, size));
                }
            } else {
                self.writeln(&format!("{} {};", base_ty, field.name.name));
            }
            // Emit companion _len field for slice-like struct fields
            if Self::is_slice_field_type(&field.ty) {
                self.writeln(&format!("size_t {}_len;", field.name.name));
            }
        }
        self.dedent();
        self.writeln(&format!("}} {};", s.name.name));
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs in C
        self.writeln(&format!("typedef struct {} {{", l.name.name));
        self.indent();
        for field in &l.fields {
            let base_ty = self.type_to_c_base(&field.ty);
            if Self::is_array_type(&field.ty) {
                if let Some(size) = Self::get_array_size(&field.ty) {
                    self.writeln(&format!("{} {}[{}];", base_ty, field.name.name, size));
                }
            } else {
                self.writeln(&format!("{} {};", base_ty, field.name.name));
            }
        }
        self.dedent();
        self.writeln(&format!("}} {};", l.name.name));
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate tag enum
        self.writeln("typedef enum {");
        self.indent();
        for (i, variant) in e.variants.iter().enumerate() {
            let comma = if i < e.variants.len() - 1 { "," } else { "" };
            self.writeln(&format!(
                "{}_{} = {}{}",
                e.name.name, variant.name.name, i, comma
            ));
        }
        self.dedent();
        self.writeln(&format!("}} {}_Tag;", e.name.name));
        self.writeln("");

        // Generate tagged union
        self.writeln("typedef struct {");
        self.indent();
        self.writeln(&format!("{}_Tag tag;", e.name.name));

        // Check if any variant has data
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
                        for (i, ty) in types.iter().enumerate() {
                            let base_ty = self.type_to_c_base(ty);
                            if Self::is_array_type(ty) {
                                if let Some(size) = Self::get_array_size(ty) {
                                    self.writeln(&format!("{} v{}[{}];", base_ty, i, size));
                                }
                            } else {
                                self.writeln(&format!("{} v{};", base_ty, i));
                            }
                        }
                        self.dedent();
                        self.writeln(&format!("}} {};", variant.name.name));
                    }
                    crate::parser::EnumVariantData::Struct(fields) => {
                        self.writeln("struct {");
                        self.indent();
                        for field in fields {
                            let base_ty = self.type_to_c_base(&field.ty);
                            if Self::is_array_type(&field.ty) {
                                if let Some(size) = Self::get_array_size(&field.ty) {
                                    self.writeln(&format!(
                                        "{} {}[{}];",
                                        base_ty, field.name.name, size
                                    ));
                                }
                            } else {
                                self.writeln(&format!("{} {};", base_ty, field.name.name));
                            }
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

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        use crate::parser::TypeKind;

        // Check if the const is an array type
        match &c.ty.kind {
            TypeKind::Array { element, size } => {
                let base_ty = self.type_to_c_base(&c.ty);
                self.write_indent();
                self.write(&format!(
                    "static const {} {}[{}] = ",
                    base_ty, c.name.name, size
                ));

                // For array constants, check if the init is a Bytes/Hex literal or an Array
                match &c.value.kind {
                    ExprKind::Bytes(s) => {
                        self.write("{");
                        for (i, b) in s.bytes().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.write(&format!("0x{:02X}", b));
                        }
                        self.write("}");
                    }
                    ExprKind::Hex(h) => {
                        self.write("{");
                        let bytes: Vec<u8> = (0..h.len())
                            .step_by(2)
                            .filter_map(|i| u8::from_str_radix(&h[i..i + 2], 16).ok())
                            .collect();
                        for (i, b) in bytes.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.write(&format!("0x{:02X}", b));
                        }
                        self.write("}");
                    }
                    _ => {
                        self.generate_expr(&c.value);
                    }
                }
                self.write(";\n");

                // For arrays, also emit a length constant
                if let TypeKind::Slice { .. } = &element.kind {
                    // skip
                } else {
                    self.writeln(&format!(
                        "static const size_t {}_len = {};",
                        c.name.name, size
                    ));
                }
            }
            _ => {
                let ty_str = self.type_to_c(&c.ty);
                self.write_indent();
                self.write(&format!("static const {} {} = ", ty_str, c.name.name));
                self.generate_expr(&c.value);
                self.write(";\n");
            }
        }
        self.writeln("");
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

    /// Get the fixed array size from a parameter type, if it's a fixed-size array (or ref to one).
    /// These decay to pointers in C and should not have `&` taken.
    fn get_fixed_array_param_size(ty: &ParserType) -> Option<u64> {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Array { size, .. } => Some(*size),
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                if let TypeKind::Array { size, .. } = &inner.kind {
                    Some(*size)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Populate pointer_vars, slice_vars, fixed_array_vars, and len_param_names from function parameters
    fn collect_pointer_params(&mut self, func: &Function) {
        self.pointer_vars.clear();
        self.slice_vars.clear();
        self.fixed_array_vars.clear();
        self.len_param_names.clear();
        self.var_renames.clear();
        for param in &func.params {
            if Self::is_pointer_param(&param.ty) {
                self.pointer_vars.insert(param.name.name.clone());
            }
            if Self::param_needs_len(&param.ty) {
                self.slice_vars.insert(param.name.name.clone());
                self.len_param_names
                    .insert(format!("{}_len", param.name.name));
            }
            if let Some(size) = Self::get_fixed_array_param_size(&param.ty) {
                self.fixed_array_vars.insert(param.name.name.clone(), size);
            }
            // Track struct types for parameters (Named, &Named, &mut Named)
            let struct_name = match &param.ty.kind {
                crate::parser::TypeKind::Named(ident) => Some(ident.name.clone()),
                crate::parser::TypeKind::MutRef(inner) | crate::parser::TypeKind::Ref(inner) => {
                    if let crate::parser::TypeKind::Named(ident) = &inner.kind {
                        Some(ident.name.clone())
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(sn) = struct_name {
                self.var_types.insert(param.name.name.clone(), sn);
            }
        }
    }

    fn generate_function(&mut self, func: &Function) {
        let ret_ty = self.return_type_to_c(func.return_type.as_ref());

        self.write_indent();
        self.write(&format!("static {} {}(", ret_ty, func.name.name));

        // Parameters
        let mut first = true;
        for param in &func.params {
            if !first {
                self.write(", ");
            }
            first = false;
            self.generate_param_decl(param);
        }

        if first {
            self.write("void");
        }

        self.write(") {\n");
        self.indent();
        self.collect_pointer_params(func);
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_method(&mut self, struct_name: &str, func: &Function) {
        let mangled_name = format!("{}__{}", struct_name, func.name.name);
        let ret_ty = self.return_type_to_c_with_self(func.return_type.as_ref(), Some(struct_name));

        self.write_indent();
        self.write(&format!("static {} {}(", ret_ty, mangled_name));

        // Parameters
        let mut first = true;
        for param in &func.params {
            if !first {
                self.write(", ");
            }
            first = false;

            // 'self' parameter: pass as pointer to the struct
            if param.name.name == "self" {
                self.write(&format!("{}* self", struct_name));
            } else {
                self.generate_param_decl(param);
            }
        }

        if first {
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

    fn generate_param_decl(&mut self, param: &crate::parser::Param) {
        use crate::parser::TypeKind;

        match &param.ty.kind {
            TypeKind::Array { element: _, size } => {
                // Fixed-size arrays decay to pointers in function params
                // No companion _len needed since the size is known at compile time
                let base = self.type_to_c_base(&param.ty);
                self.write(&format!("const {}* {}", base, param.name.name));
                let _ = size;
            }
            TypeKind::Slice { element } => {
                // Slice: pointer + length
                let elem_ty = self.type_to_c(element);
                self.write(&format!("const {}* {}", elem_ty, param.name.name));
                self.write(&format!(", size_t {}_len", param.name.name));
            }
            TypeKind::ArrayRef { element, size } => {
                // Reference to fixed-size array: pointer
                let elem_ty = self.type_to_c(element);
                self.write(&format!("const {}* {}", elem_ty, param.name.name));
                self.write(&format!(", size_t {}_len", param.name.name));
                let _ = size;
            }
            TypeKind::MutRef(inner) => match &inner.kind {
                TypeKind::Slice { element } => {
                    let elem_ty = self.type_to_c(element);
                    self.write(&format!("{}* {}", elem_ty, param.name.name));
                    self.write(&format!(", size_t {}_len", param.name.name));
                }
                TypeKind::Array { element, size } => {
                    // Fixed-size array ref: no companion _len needed
                    let elem_ty = self.type_to_c(element);
                    self.write(&format!("{}* {}", elem_ty, param.name.name));
                    let _ = size;
                }
                TypeKind::Named(ident) => {
                    self.write(&format!("{}* {}", ident.name, param.name.name));
                }
                _ => {
                    let ty_str = self.type_to_c(inner);
                    self.write(&format!("{}* {}", ty_str, param.name.name));
                }
            },
            TypeKind::Ref(inner) => match &inner.kind {
                TypeKind::Slice { element } => {
                    let elem_ty = self.type_to_c(element);
                    self.write(&format!("const {}* {}", elem_ty, param.name.name));
                    self.write(&format!(", size_t {}_len", param.name.name));
                }
                TypeKind::Array { element, size } => {
                    // Fixed-size array ref: no companion _len needed
                    let elem_ty = self.type_to_c(element);
                    self.write(&format!("const {}* {}", elem_ty, param.name.name));
                    let _ = size;
                }
                TypeKind::Named(ident) => {
                    self.write(&format!("const {}* {}", ident.name, param.name.name));
                }
                _ => {
                    let ty_str = self.type_to_c(inner);
                    self.write(&format!("const {}* {}", ty_str, param.name.name));
                }
            },
            TypeKind::Named(ident) => {
                self.write(&format!("{} {}", ident.name, param.name.name));
            }
            _ => {
                let ty_str = self.type_to_c(&param.ty);
                self.write(&format!("{} {}", ty_str, param.name.name));
            }
        }
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.pointer_vars.clear();
        self.slice_vars.clear();
        self.fixed_array_vars.clear();
        self.len_param_names.clear();
        self.var_renames.clear();
        self.writeln(&format!("static void test_{}(void) {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
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

                self.generate_let_stmt(name, ty.as_ref(), init.as_ref());
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
                        let native = p.to_native();
                        let write_fn = match (native, endian) {
                            (
                                crate::parser::PrimitiveType::U16
                                | crate::parser::PrimitiveType::I16,
                                crate::parser::Endianness::Big,
                            ) => "__algoc_write_u16be",
                            (
                                crate::parser::PrimitiveType::U16
                                | crate::parser::PrimitiveType::I16,
                                crate::parser::Endianness::Little,
                            ) => "__algoc_write_u16le",
                            (
                                crate::parser::PrimitiveType::U32
                                | crate::parser::PrimitiveType::I32,
                                crate::parser::Endianness::Big,
                            ) => "__algoc_write_u32be",
                            (
                                crate::parser::PrimitiveType::U32
                                | crate::parser::PrimitiveType::I32,
                                crate::parser::Endianness::Little,
                            ) => "__algoc_write_u32le",
                            (
                                crate::parser::PrimitiveType::U64
                                | crate::parser::PrimitiveType::I64,
                                crate::parser::Endianness::Big,
                            ) => "__algoc_write_u64be",
                            (
                                crate::parser::PrimitiveType::U64
                                | crate::parser::PrimitiveType::I64,
                                crate::parser::Endianness::Little,
                            ) => "__algoc_write_u64le",
                            (
                                crate::parser::PrimitiveType::U128
                                | crate::parser::PrimitiveType::I128,
                                crate::parser::Endianness::Big,
                            ) => "__algoc_write_u128be",
                            (
                                crate::parser::PrimitiveType::U128
                                | crate::parser::PrimitiveType::I128,
                                crate::parser::Endianness::Little,
                            ) => "__algoc_write_u128le",
                            _ => "__algoc_write_u32be",
                        };
                        self.write_indent();
                        self.write(&format!("{}(", write_fn));
                        self.generate_expr(array);
                        self.write(" + ");
                        self.generate_expr(start);
                        self.write(", ");
                        self.generate_expr(value);
                        self.write(");\n");
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
                self.write(&format!("for (size_t {} = ", var.name));
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

    fn generate_let_stmt(
        &mut self,
        name: &crate::parser::Ident,
        ty: Option<&ParserType>,
        init: Option<&Expr>,
    ) {
        use crate::parser::TypeKind;

        // Check if this variable name conflicts with a generated _len parameter companion.
        // If so, rename to avoid redeclaration errors in C.
        let effective_name = if self.len_param_names.contains(&name.name) {
            let renamed = format!("_local_{}", name.name);
            self.var_renames.insert(name.name.clone(), renamed.clone());
            renamed
        } else {
            name.name.clone()
        };
        // Use a temporary Ident-like struct for generating with the effective name
        let name_str = &effective_name;

        match ty {
            Some(ty) => match &ty.kind {
                TypeKind::Array { element, size } => {
                    let base_ty = self.type_to_c_base(ty);
                    self.write_indent();
                    self.write(&format!("{} {}[{}]", base_ty, name_str, size));

                    if let Some(init) = init {
                        match &init.kind {
                            ExprKind::ArrayRepeat { value, .. } => {
                                // Check if value is 0 - use = {0}
                                if is_zero_value(value) {
                                    self.write(" = {0}");
                                } else {
                                    self.write(";\n");
                                    // Use a loop to fill
                                    self.write_indent();
                                    self.write(&format!(
                                        "for (size_t __i = 0; __i < {}; __i++) {}[__i] = ",
                                        size, name_str
                                    ));
                                    self.generate_expr(value);
                                    // No semicolon - we add it below
                                }
                            }
                            ExprKind::Array(elements) => {
                                self.write(" = {");
                                for (i, elem) in elements.iter().enumerate() {
                                    if i > 0 {
                                        self.write(", ");
                                    }
                                    self.generate_expr(elem);
                                }
                                self.write("}");
                            }
                            ExprKind::Bytes(s) => {
                                self.write(" = {");
                                for (i, b) in s.bytes().enumerate() {
                                    if i > 0 {
                                        self.write(", ");
                                    }
                                    self.write(&format!("0x{:02X}", b));
                                }
                                self.write("}");
                            }
                            ExprKind::Hex(h) => {
                                self.write(" = {");
                                let bytes: Vec<u8> = (0..h.len())
                                    .step_by(2)
                                    .filter_map(|i| u8::from_str_radix(&h[i..i + 2], 16).ok())
                                    .collect();
                                for (i, b) in bytes.iter().enumerate() {
                                    if i > 0 {
                                        self.write(", ");
                                    }
                                    self.write(&format!("0x{:02X}", b));
                                }
                                self.write("}");
                            }
                            _ => {
                                // For other expressions, try memcpy for arrays
                                self.write(";\n");
                                self.write_indent();
                                self.write(&format!("memcpy({}, ", name_str));
                                self.generate_expr(init);
                                self.write(&format!(", sizeof({}))", name_str));
                            }
                        }
                    } else {
                        self.write(" = {0}");
                    }
                    self.write(";\n");

                    // Fixed-size arrays don't need a companion _len variable
                    // since the size is known at compile time
                    self.fixed_array_vars.insert(name.name.clone(), *size);
                    let _ = element;
                }
                TypeKind::Slice { element } => {
                    // Slices: pointer + length
                    let elem_ty = self.type_to_c(element);
                    // Check if init is a read_chunk call (needs out_len parameter)
                    let is_read_chunk = init.is_some_and(|e| {
                        if let ExprKind::MethodCall { method_name, .. } = &e.kind {
                            method_name == "read_chunk"
                        } else if let ExprKind::Call { func, .. } = &e.kind {
                            if let ExprKind::Field { field, .. } = &func.kind {
                                field.name == "read_chunk"
                            } else if let ExprKind::Ident(ident) = &func.kind {
                                ident.name.contains("read_chunk")
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    });
                    if is_read_chunk {
                        // Declare _len first, then call with &name_len
                        self.writeln(&format!("size_t {}_len = 0;", name_str));
                        self.write_indent();
                        self.write(&format!("{}* {} = ({}*)", elem_ty, name_str, elem_ty));
                        if let Some(init) = init {
                            self.generate_read_chunk_call(init, name_str);
                        }
                        self.write(";\n");
                    } else {
                        self.write_indent();
                        if let Some(init) = init {
                            self.write(&format!("{}* {} = ({}*)", elem_ty, name_str, elem_ty));
                            self.generate_expr(init);
                            self.write(";\n");
                            // Initialize _len from the init expression
                            self.write_indent();
                            self.write(&format!("size_t {}_len = ", name_str));
                            self.generate_arg_len_expr(init);
                            self.write(";\n");
                        } else {
                            self.write(&format!("{}* {} = NULL;\n", elem_ty, name_str));
                            self.writeln(&format!("size_t {}_len = 0;", name_str));
                        }
                    }
                    self.slice_vars.insert(name.name.clone());
                }
                TypeKind::Named(ident) => {
                    self.write_indent();
                    self.write(&format!("{} {}", ident.name, name_str));
                    if let Some(init) = init {
                        self.write(" = ");
                        self.generate_expr(init);
                    } else {
                        self.write(" = {0}");
                    }
                    self.write(";\n");
                }
                TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                    // Reference types become pointers
                    match &inner.kind {
                        TypeKind::Slice { element } => {
                            let elem_ty = self.type_to_c(element);
                            let is_const = matches!(ty.kind, crate::parser::TypeKind::Ref(_));
                            // Check if init is a read_chunk call
                            let is_read_chunk = init.is_some_and(|e| {
                                if let ExprKind::MethodCall { method_name, .. } = &e.kind {
                                    method_name == "read_chunk"
                                } else if let ExprKind::Call { func, .. } = &e.kind {
                                    if let ExprKind::Ident(ident) = &func.kind {
                                        ident.name.contains("read_chunk")
                                    } else {
                                        false
                                    }
                                } else {
                                    false
                                }
                            });
                            if is_read_chunk {
                                // Declare _len first, then call with &name_len
                                self.writeln(&format!("size_t {}_len = 0;", name_str));
                                self.write_indent();
                                if is_const {
                                    self.write("const ");
                                }
                                self.write(&format!("{}* {} = ({}*)", elem_ty, name_str, elem_ty));
                                if let Some(init) = init {
                                    self.generate_read_chunk_call(init, name_str);
                                }
                                self.write(";\n");
                            } else {
                                self.write_indent();
                                if is_const {
                                    self.write("const ");
                                }
                                self.write(&format!("{}* {}", elem_ty, name_str));
                                if let Some(init) = init {
                                    self.write(" = ");
                                    self.generate_expr(init);
                                    self.write(";\n");
                                    self.write_indent();
                                    self.write(&format!("size_t {}_len = ", name_str));
                                    self.generate_arg_len_expr(init);
                                    self.write(";\n");
                                } else {
                                    self.write(" = NULL;\n");
                                    self.writeln(&format!("size_t {}_len = 0;", name_str));
                                }
                            }
                            self.slice_vars.insert(name.name.clone());
                        }
                        TypeKind::Array { element, .. } => {
                            // Reference to fixed-size array: pointer, no _len needed
                            let elem_ty = self.type_to_c(element);
                            self.write_indent();
                            if matches!(ty.kind, crate::parser::TypeKind::Ref(_)) {
                                self.write("const ");
                            }
                            self.write(&format!("{}* {}", elem_ty, name_str));
                            if let Some(init) = init {
                                self.write(" = ");
                                self.generate_expr(init);
                            } else {
                                self.write(" = NULL");
                            }
                            self.write(";\n");
                        }
                        TypeKind::Named(ident) => {
                            self.write_indent();
                            if matches!(ty.kind, crate::parser::TypeKind::Ref(_)) {
                                self.write("const ");
                            }
                            self.write(&format!("{}* {}", ident.name, name_str));
                            if let Some(init) = init {
                                self.write(" = ");
                                self.generate_expr(init);
                            } else {
                                self.write(" = NULL");
                            }
                            self.write(";\n");
                        }
                        _ => {
                            let inner_ty = self.type_to_c(inner);
                            self.write_indent();
                            if matches!(ty.kind, crate::parser::TypeKind::Ref(_)) {
                                self.write("const ");
                            }
                            self.write(&format!("{}* {}", inner_ty, name_str));
                            if let Some(init) = init {
                                self.write(" = ");
                                self.generate_expr(init);
                            } else {
                                self.write(" = NULL");
                            }
                            self.write(";\n");
                        }
                    }
                }
                TypeKind::ArrayRef { element, size } => {
                    let elem_ty = self.type_to_c(element);
                    self.write_indent();
                    self.write(&format!("const {}* {}", elem_ty, name_str));
                    if let Some(init) = init {
                        self.write(" = ");
                        self.generate_expr(init);
                    } else {
                        self.write(" = NULL");
                    }
                    self.write(";\n");
                    self.writeln(&format!("size_t {}_len = {};", name_str, size));
                    self.slice_vars.insert(name.name.clone());
                }
                _ => {
                    let ty_str = self.type_to_c(ty);
                    self.write_indent();
                    self.write(&format!("{} {}", ty_str, name_str));
                    if let Some(init) = init {
                        self.write(" = ");
                        self.generate_expr(init);
                    } else {
                        self.write(&format!(" = {}", self.default_value_for_type(ty)));
                    }
                    self.write(";\n");
                }
            },
            None => {
                // No type annotation - infer from init
                if let Some(init) = init {
                    match &init.kind {
                        ExprKind::Hex(h) => {
                            let byte_count = h.len() / 2;
                            let bytes: Vec<u8> = (0..h.len())
                                .step_by(2)
                                .filter_map(|i| u8::from_str_radix(&h[i..i + 2], 16).ok())
                                .collect();
                            self.write_indent();
                            self.write(&format!("const uint8_t {}[{}] = {{", name_str, byte_count));
                            for (i, b) in bytes.iter().enumerate() {
                                if i > 0 {
                                    self.write(", ");
                                }
                                self.write(&format!("0x{:02X}", b));
                            }
                            self.write("};\n");
                            self.fixed_array_vars
                                .insert(name.name.clone(), byte_count as u64);
                        }
                        ExprKind::Bytes(s) => {
                            let byte_count = s.len();
                            self.write_indent();
                            self.write(&format!("const uint8_t {}[{}] = {{", name_str, byte_count));
                            for (i, b) in s.as_bytes().iter().enumerate() {
                                if i > 0 {
                                    self.write(", ");
                                }
                                self.write(&format!("0x{:02X}", b));
                            }
                            self.write("};\n");
                            self.fixed_array_vars
                                .insert(name.name.clone(), byte_count as u64);
                        }
                        ExprKind::String(s) => {
                            let byte_count = s.len();
                            self.write_indent();
                            self.write(&format!("const uint8_t {}[{}] = {{", name_str, byte_count));
                            for (i, b) in s.as_bytes().iter().enumerate() {
                                if i > 0 {
                                    self.write(", ");
                                }
                                self.write(&format!("0x{:02X}", b));
                            }
                            self.write("};\n");
                            self.fixed_array_vars
                                .insert(name.name.clone(), byte_count as u64);
                        }
                        ExprKind::Slice { .. } => {
                            // Slice expression like data[offset..offset+64] - treat as const uint8_t*
                            self.write_indent();
                            self.write(&format!("const uint8_t* {} = ", name_str));
                            self.generate_expr(init);
                            self.write(";\n");
                            self.write_indent();
                            self.write(&format!("size_t {}_len = ", name_str));
                            self.generate_arg_len_expr(init);
                            self.write(";\n");
                            self.slice_vars.insert(name.name.clone());
                        }
                        _ => {
                            let inferred_ty = self.infer_c_type(init);
                            self.write_indent();
                            self.write(&format!("{} {} = ", inferred_ty, name_str));
                            self.generate_expr(init);
                            self.write(";\n");
                        }
                    }
                } else {
                    // No type, no init - default to int
                    self.write_indent();
                    self.write(&format!("int {} = 0;\n", name_str));
                }
            }
        }
    }

    /// Generate a read_chunk call with an extra &name_len out parameter
    fn generate_read_chunk_call(&mut self, init: &Expr, name_str: &str) {
        match &init.kind {
            ExprKind::MethodCall {
                receiver,
                method_name: mname,
                mangled_name,
                args,
            } => {
                let func_name = if !mangled_name.is_empty() {
                    mangled_name.clone()
                } else if let ExprKind::Ident(obj_ident) = &receiver.kind {
                    if let Some(sn) = self.var_types.get(&obj_ident.name).cloned() {
                        format!("{}__{}", sn, mname)
                    } else {
                        format!("{}_{}", obj_ident.name, mname)
                    }
                } else {
                    mname.clone()
                };
                self.write(&format!("{}(", func_name));
                self.write("&");
                self.generate_expr(receiver);
                for arg in args {
                    self.write(", ");
                    self.generate_expr(arg);
                }
                self.write(&format!(", &{}_len)", name_str));
            }
            ExprKind::Call { func, args } => {
                // For reader.read_chunk() calls, func is Field { object, field: read_chunk }
                if let ExprKind::Field { object, field } = &func.kind {
                    // Generate: Reader_read_chunk(&object, args..., &name_len)
                    self.write(&format!("Reader_{}", field.name));
                    self.write("(");
                    let is_ptr = matches!(&object.kind, ExprKind::Ident(ident) if self.pointer_vars.contains(&ident.name));
                    if !is_ptr {
                        self.write("&");
                    }
                    self.generate_expr(object);
                    for arg in args {
                        self.write(", ");
                        self.generate_expr(arg);
                    }
                    self.write(&format!(", &{}_len)", name_str));
                } else {
                    self.generate_expr(func);
                    self.write("(");
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(arg);
                    }
                    self.write(&format!(", &{}_len)", name_str));
                }
            }
            _ => {
                self.generate_expr(init);
            }
        }
    }

    /// Infer C type from an expression
    fn infer_c_type(&self, expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Integer(n) => {
                if *n <= 0xFF {
                    "uint8_t".to_string()
                } else if *n <= 0xFFFF {
                    "uint16_t".to_string()
                } else if *n <= 0xFFFFFFFF {
                    "uint32_t".to_string()
                } else if *n <= 0xFFFFFFFFFFFFFFFF {
                    "uint64_t".to_string()
                } else {
                    "__uint128_t".to_string()
                }
            }
            ExprKind::Bool(_) => "bool".to_string(),
            ExprKind::Paren(inner) => self.infer_c_type(inner),
            ExprKind::Cast { ty, .. } => self.type_to_c(ty),
            ExprKind::StructLit { name, .. } => name.name.clone(),
            ExprKind::TypeStaticCall {
                type_name,
                method_name,
                ..
            } => {
                if method_name.name == "new" {
                    type_name.name.clone()
                } else {
                    "uint64_t".to_string()
                }
            }
            ExprKind::Call { func, .. } => {
                if let ExprKind::Ident(ident) = &func.kind
                    && let Some(idx) = ident.name.find("__new")
                {
                    return ident.name[..idx].to_string();
                }
                "uint32_t".to_string()
            }
            _ => "uint32_t".to_string(),
        }
    }

    /// Generate a function call argument, and if the corresponding parameter
    /// needs a companion _len argument, emit that too.
    fn generate_call_arg(&mut self, arg: &Expr, needs_len: bool) {
        self.generate_expr(arg);
        if needs_len {
            self.write(", ");
            self.generate_arg_len_expr(arg);
        }
    }

    /// Generate the length expression for an argument being passed to a slice/array parameter.
    /// This figures out the correct length based on the argument expression form.
    fn generate_arg_len_expr(&mut self, arg: &Expr) {
        match &arg.kind {
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // &array or &mut array - use the inner expression's length
                self.generate_arg_len_expr(inner);
            }
            ExprKind::Ident(ident) => {
                if let Some(&size) = self.fixed_array_vars.get(&ident.name) {
                    // Fixed-size array: use the known compile-time size
                    self.write(&format!("{}", size));
                } else {
                    // Variable - use companion _len variable (with rename if applicable)
                    let effective = self
                        .var_renames
                        .get(&ident.name)
                        .cloned()
                        .unwrap_or_else(|| ident.name.clone());
                    self.write(&format!("{}_len", effective));
                }
            }
            ExprKind::Field { object, field } => {
                // Check if this field is a fixed-size array in the struct definition
                // Use byte count (element_count * element_size) for secure_zero etc.
                if let Some(byte_count) = self.get_struct_field_byte_count(object, &field.name) {
                    self.write(&format!("{}", byte_count));
                } else {
                    // struct.field - use struct.field_len
                    let accessor = if let ExprKind::Ident(ident) = &object.kind
                        && self.pointer_vars.contains(&ident.name)
                    {
                        "->"
                    } else {
                        "."
                    };
                    self.generate_expr(object);
                    self.write(&format!("{}{}_len", accessor, field.name));
                }
            }
            ExprKind::Slice {
                start,
                end,
                inclusive,
                ..
            } => {
                // array[start..end] - length is (end - start)
                self.write("(");
                self.generate_expr(end);
                if *inclusive {
                    self.write(" + 1");
                }
                self.write(" - ");
                self.generate_expr(start);
                self.write(")");
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("{}", s.len()));
            }
            ExprKind::Hex(h) => {
                self.write(&format!("{}", h.len() / 2));
            }
            ExprKind::String(s) => {
                self.write(&format!("{}", s.len()));
            }
            ExprKind::Array(elements) => {
                self.write(&format!("{}", elements.len()));
            }
            ExprKind::Paren(inner) => {
                self.generate_arg_len_expr(inner);
            }
            _ => {
                // Fallback
                self.write("0");
            }
        }
    }

    /// Generate function call arguments, looking up the function signature to
    /// determine which arguments need companion _len parameters.
    fn generate_call_args(&mut self, func_name: &str, args: &[Expr]) {
        if let Some(params) = self.func_signatures.get(func_name).cloned() {
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                let needs_len = params.get(i).is_some_and(|p| p.needs_len);
                self.generate_call_arg(arg, needs_len);
            }
        } else {
            // No known signature - just generate args normally
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.generate_expr(arg);
            }
        }
    }

    /// Generate function call arguments for a method call, where the first C parameter
    /// is the self/receiver (already emitted), and the remaining args map to params[1..].
    fn generate_method_call_args(&mut self, func_name: &str, args: &[Expr]) {
        if let Some(params) = self.func_signatures.get(func_name).cloned() {
            for (i, arg) in args.iter().enumerate() {
                self.write(", ");
                // args[i] corresponds to params[i+1] (params[0] is self)
                let needs_len = params.get(i + 1).is_some_and(|p| p.needs_len);
                self.generate_call_arg(arg, needs_len);
            }
        } else {
            for arg in args {
                self.write(", ");
                self.generate_expr(arg);
            }
        }
    }

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                if *n > 0xFFFFFFFFFFFFFFFF {
                    // u128 literal: split into two 64-bit parts
                    let hi = (*n >> 64) as u64;
                    let lo = *n as u64;
                    self.write(&format!(
                        "((__uint128_t)0x{:X}ULL << 64 | (__uint128_t)0x{:X}ULL)",
                        hi, lo
                    ));
                } else if *n > 0xFFFFFFFF {
                    self.write(&format!("{}ULL", n));
                } else if *n > 0x7FFFFFFF {
                    self.write(&format!("{}U", n));
                } else {
                    self.write(&format!("{}", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // Strings become uint8_t arrays with known length
                // Generate as a compound literal
                self.write("(const uint8_t*)\"");
                self.write(&escape_c_string(s));
                self.write("\"");
            }
            ExprKind::Bytes(s) => {
                // Byte literal: generate as compound literal uint8_t array
                self.write("(const uint8_t[");
                self.write(&format!("{}", s.len()));
                self.write("]){");
                for (i, b) in s.bytes().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("0x{:02X}", b));
                }
                self.write("}");
            }
            ExprKind::Hex(h) => {
                // Hex literal: generate as compound literal uint8_t array
                let bytes: Vec<u8> = (0..h.len())
                    .step_by(2)
                    .filter_map(|i| u8::from_str_radix(&h[i..i + 2], 16).ok())
                    .collect();
                self.write("(const uint8_t[");
                self.write(&format!("{}", bytes.len()));
                self.write("]){");
                for (i, b) in bytes.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("0x{:02X}", b));
                }
                self.write("}");
            }
            ExprKind::Ident(ident) => {
                // Check if this variable was renamed to avoid _len parameter conflicts
                if let Some(renamed) = self.var_renames.get(&ident.name).cloned() {
                    self.write(&renamed);
                } else {
                    self.write(&ident.name);
                }
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
                        self.generate_array_len_expr(left);
                        self.write(", ");
                        self.generate_expr(right);
                        self.write(", ");
                        self.generate_array_len_expr(right);
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
                // Array slicing: pass array + start as pointer
                // This generates just the pointer; length must be handled by context
                self.write("(");
                self.generate_expr(array);
                self.write(" + ");
                self.generate_expr(start);
                self.write(")");
            }
            ExprKind::Field { object, field } => {
                // Check if the object is a pointer variable (from &mut / & params)
                if let ExprKind::Ident(ident) = &object.kind
                    && self.pointer_vars.contains(&ident.name)
                {
                    self.generate_expr(object);
                    self.write(&format!("->{}", field.name));
                    return;
                }
                self.generate_expr(object);
                self.write(&format!(".{}", field.name));
            }
            ExprKind::Call { func, args } => {
                // Check for Reader/Writer constructor calls
                if let ExprKind::Ident(ident) = &func.kind {
                    if ident.name == "Reader" {
                        self.write("Reader_new(");
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_call_arg(arg, true);
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
                            self.generate_call_arg(arg, true);
                        }
                        self.write(")");
                        return;
                    }
                }

                // Check for method calls like slice.len() or reader.read_u32()
                if let ExprKind::Field { object, field } = &func.kind {
                    if field.name == "len" && args.is_empty() {
                        // Convert .len() to companion _len variable or fixed array size
                        if let ExprKind::Ident(ident) = &object.kind {
                            if let Some(&size) = self.fixed_array_vars.get(&ident.name) {
                                self.write(&format!("{}", size));
                            } else {
                                let effective = self
                                    .var_renames
                                    .get(&ident.name)
                                    .cloned()
                                    .unwrap_or_else(|| ident.name.clone());
                                self.write(&format!("{}_len", effective));
                            }
                        } else if let ExprKind::Field {
                            object: inner_obj,
                            field: inner_field,
                        } = &object.kind
                        {
                            // Handle struct.field.len()
                            // Check if this field is a fixed-size array in the struct
                            if let Some(size) =
                                self.get_struct_field_array_size(inner_obj, &inner_field.name)
                            {
                                self.write(&format!("{}", size));
                            } else {
                                let accessor = if let ExprKind::Ident(ident) = &inner_obj.kind
                                    && self.pointer_vars.contains(&ident.name)
                                {
                                    "->"
                                } else {
                                    "."
                                };
                                self.generate_expr(inner_obj);
                                self.write(&format!("{}{}_len", accessor, inner_field.name));
                            }
                        } else {
                            // Fallback - might not work for complex expressions
                            self.write("/* .len() */ 0");
                        }
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

                    // Reader/Writer method calls
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

                    if reader_methods.contains(&field.name.as_str()) {
                        // Determine the class name for the method
                        let method_c_name = format!("Reader_{}", field.name);
                        // If the object is already a pointer, don't take its address
                        let is_ptr = matches!(&object.kind, ExprKind::Ident(ident) if self.pointer_vars.contains(&ident.name));
                        if is_ptr {
                            self.write(&format!("{}(", method_c_name));
                        } else {
                            self.write(&format!("{}(&", method_c_name));
                        }
                        self.generate_expr(object);
                        for arg in args {
                            self.write(", ");
                            self.generate_expr(arg);
                        }
                        self.write(")");
                        return;
                    }
                    if writer_methods.contains(&field.name.as_str()) {
                        let method_c_name = format!("Writer_{}", field.name);
                        let is_ptr = matches!(&object.kind, ExprKind::Ident(ident) if self.pointer_vars.contains(&ident.name));
                        if is_ptr {
                            self.write(&format!("{}(", method_c_name));
                        } else {
                            self.write(&format!("{}(&", method_c_name));
                        }
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
                        self.generate_method_call_args(&mangled_name, args);
                        self.write(")");
                        return;
                    }
                }

                // Extract function name for signature lookup
                let func_name = if let ExprKind::Ident(ident) = &func.kind {
                    Some(ident.name.clone())
                } else {
                    None
                };
                self.generate_expr(func);
                self.write("(");
                if let Some(ref name) = func_name {
                    self.generate_call_args(name, args);
                } else {
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(arg);
                    }
                }
                self.write(")");
            }
            ExprKind::Builtin { name, args } => {
                self.generate_builtin(*name, args);
            }
            ExprKind::Array(elements) => {
                // Array literal as compound literal
                if elements.is_empty() {
                    self.write("{0}");
                } else {
                    self.write("{");
                    for (i, elem) in elements.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(elem);
                    }
                    self.write("}");
                }
            }
            ExprKind::ArrayRepeat { value, count: _ } => {
                // [value; count] - In expression context, use compound literal with memset for zero
                // This is tricky in C - best handled at declaration sites
                // For expression context, generate a helper
                if is_zero_value(value) {
                    self.write("{0}");
                } else {
                    // Fallback: generate initializer (works for small known sizes)
                    self.write("{");
                    self.generate_expr(value);
                    self.write("}");
                }
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // &/&mut in C: take address
                // But for fixed-size arrays, the name already decays to a pointer
                match &inner.kind {
                    ExprKind::Ident(ident)
                        if self.fixed_array_vars.contains_key(&ident.name)
                            || self.slice_vars.contains(&ident.name) =>
                    {
                        self.generate_expr(inner);
                    }
                    ExprKind::Field { object, field } => {
                        // Check if this struct field is a fixed-size array
                        // If so, it already decays to a pointer in C (no & needed)
                        // For non-u8 arrays, we also need a (uint8_t*) cast
                        use crate::parser::{PrimitiveType, TypeKind};
                        let field_array_info: Option<(u64, bool)> = (|| {
                            let struct_name = if let ExprKind::Ident(ident) = &object.kind {
                                self.var_types.get(&ident.name)?.clone()
                            } else {
                                return None;
                            };
                            let fields = self.struct_defs.get(&struct_name)?;
                            let fi = fields.iter().find(|f| f.name == field.name)?;
                            if let TypeKind::Array { element, size } = &fi.ty.kind {
                                let is_u8 =
                                    matches!(element.kind, TypeKind::Primitive(PrimitiveType::U8));
                                Some((*size, is_u8))
                            } else {
                                None
                            }
                        })();
                        if let Some((_size, is_u8)) = field_array_info {
                            // Array field: already decays to pointer, no & needed
                            if !is_u8 {
                                self.write("(uint8_t*)");
                            }
                            self.generate_expr(inner);
                        } else {
                            self.write("&");
                            self.generate_expr(inner);
                        }
                    }
                    ExprKind::Ident(_) => {
                        self.write("&");
                        self.generate_expr(inner);
                    }
                    _ => {
                        self.generate_expr(inner);
                    }
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
                // C designated initializer
                self.write(&format!("({}){{", name.name));
                let struct_fields = self.struct_defs.get(&name.name).cloned();
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!(".{} = ", field_name.name));
                    self.generate_expr(value);
                    // If this field has a companion _len field in the struct,
                    // also emit it based on the value expression
                    if let Some(ref sfields) = struct_fields
                        && let Some(field_info) = sfields.iter().find(|f| f.name == field_name.name)
                        && Self::is_slice_field_type(&field_info.ty)
                    {
                        self.write(&format!(", .{}_len = ", field_name.name));
                        self.generate_arg_len_expr(value);
                    }
                }
                self.write("}");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // C ternary: condition ? then : else
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
                // Generate enum variant construction using designated initializers
                if args.is_empty() {
                    self.write(&format!(
                        "({}){{ .tag = {}_{}",
                        enum_name.name, enum_name.name, variant_name.name
                    ));
                } else {
                    self.write(&format!(
                        "({}){{ .tag = {}_{}, .data.{} = {{",
                        enum_name.name, enum_name.name, variant_name.name, variant_name.name
                    ));
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.write(&format!(".v{} = ", i));
                        self.generate_expr(arg);
                    }
                    self.write("}");
                }
                self.write(" }");
            }
            ExprKind::Match { expr, arms } => {
                // Generate match as a GCC statement expression ({ ...; result; })
                // This is a GNU C extension but widely supported
                self.write("({");
                self.write(" __typeof__(");
                // We need to figure out the type for the temp variable.
                // Use first arm's body to determine it.
                self.generate_expr(expr);
                self.write(") __match_scrutinee = ");
                self.generate_expr(expr);
                self.write("; ");

                // Use __typeof__ of the first arm's body for the result
                // Generate if-else chain
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write(" else ");
                    }
                    self.generate_pattern_match(&arm.pattern, "__match_scrutinee");
                    self.write(" __match_result = ");
                    self.generate_expr(&arm.body);
                    self.write("; }");
                }
                // Add a default
                if !arms
                    .iter()
                    .any(|a| matches!(a.pattern.kind, crate::parser::PatternKind::Wildcard))
                {
                    // If no wildcard, add a fallthrough (shouldn't happen in well-typed programs)
                }
                self.write(" __match_result; })");
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
                self.generate_method_call_args(mangled_name, args);
                self.write(")");
            }
            ExprKind::TypeStaticCall {
                type_name,
                method_name,
                args,
            } => {
                // Should be resolved by monomorphization
                let mangled = format!("{}__{}", type_name.name, method_name.name);
                self.write(&mangled);
                self.write("(");
                self.generate_call_args(&mangled, args);
                self.write(")");
            }
            ExprKind::GenericCall { func, args, .. } => {
                // Should be resolved by monomorphization - generate as regular call
                let func_name = if let ExprKind::Ident(ident) = &func.kind {
                    Some(ident.name.clone())
                } else {
                    None
                };
                self.generate_expr(func);
                self.write("(");
                if let Some(ref name) = func_name {
                    self.generate_call_args(name, args);
                } else {
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(arg);
                    }
                }
                self.write(")");
            }
        }
    }

    /// Generate the length expression for an array-like expression
    fn generate_array_len_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Ident(ident) => {
                if let Some(&size) = self.fixed_array_vars.get(&ident.name) {
                    // Fixed-size array: use the known compile-time size
                    self.write(&format!("{}", size));
                } else {
                    let effective = self
                        .var_renames
                        .get(&ident.name)
                        .cloned()
                        .unwrap_or_else(|| ident.name.clone());
                    self.write(&format!("{}_len", effective));
                }
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("{}", s.len()));
            }
            ExprKind::Hex(h) => {
                self.write(&format!("{}", h.len() / 2));
            }
            ExprKind::String(s) => {
                self.write(&format!("{}", s.len()));
            }
            ExprKind::Array(elements) => {
                self.write(&format!("{}", elements.len()));
            }
            ExprKind::Slice {
                start,
                end,
                inclusive,
                ..
            } => {
                self.write("(");
                self.generate_expr(end);
                if *inclusive {
                    self.write(" + 1");
                }
                self.write(" - ");
                self.generate_expr(start);
                self.write(")");
            }
            ExprKind::Field { object, field } => {
                // Check if this field is a fixed-size array in the struct definition
                // Use byte count (element_count * element_size)
                if let Some(byte_count) = self.get_struct_field_byte_count(object, &field.name) {
                    self.write(&format!("{}", byte_count));
                } else {
                    // Try object.field_len (use -> for pointer vars)
                    let accessor = if let ExprKind::Ident(ident) = &object.kind
                        && self.pointer_vars.contains(&ident.name)
                    {
                        "->"
                    } else {
                        "."
                    };
                    self.generate_expr(object);
                    self.write(&format!("{}{}_len", accessor, field.name));
                }
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) | ExprKind::Paren(inner) => {
                self.generate_array_len_expr(inner);
            }
            _ => {
                // Fallback
                self.write("0");
            }
        }
    }

    fn generate_pattern_match(&mut self, pattern: &crate::parser::Pattern, scrutinee: &str) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("if (1) {");
            }
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("if ({} == ", scrutinee));
                self.generate_expr(lit_expr);
                self.write(") {");
            }
            PatternKind::Ident(ident) => {
                // Binding pattern - always matches, bind the value
                self.write(&format!(
                    "if (1) {{ __typeof__({}) {} = {};",
                    scrutinee, ident.name, scrutinee
                ));
            }
            PatternKind::EnumVariant {
                enum_name: _,
                variant_name,
                bindings,
            } => {
                self.write(&format!("if ({}.tag == {}", scrutinee, variant_name.name));
                // Note: for a real tagged union we'd check against the enum tag constant
                // Using just the variant name here - caller should have generated enum tag constants
                self.write(") {");

                // Extract bindings
                for (i, binding) in bindings.iter().enumerate() {
                    if let PatternKind::Ident(bind_ident) = &binding.kind {
                        self.write(&format!(
                            " __typeof__({}.data.{}.v{}) {} = {}.data.{}.v{};",
                            scrutinee,
                            variant_name.name,
                            i,
                            bind_ident.name,
                            scrutinee,
                            variant_name.name,
                            i
                        ));
                    }
                }
            }
            PatternKind::Tuple(_patterns) => {
                self.write("if (1) {");
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
                self.write(") {");
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
                self.write("__algoc_assert(");
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
                let little_endian = endian == Endianness::Little;

                // Check if source is a slice/array (byte conversion)
                if is_byte_sequence_expr(expr) {
                    let read_fn = match (native, little_endian) {
                        (PrimitiveType::U16 | PrimitiveType::I16, false) => "__algoc_read_u16be",
                        (PrimitiveType::U16 | PrimitiveType::I16, true) => "__algoc_read_u16le",
                        (PrimitiveType::U32 | PrimitiveType::I32, false) => "__algoc_read_u32be",
                        (PrimitiveType::U32 | PrimitiveType::I32, true) => "__algoc_read_u32le",
                        (PrimitiveType::U64 | PrimitiveType::I64, false) => "__algoc_read_u64be",
                        (PrimitiveType::U64 | PrimitiveType::I64, true) => "__algoc_read_u64le",
                        (PrimitiveType::U128 | PrimitiveType::I128, false) => "__algoc_read_u128be",
                        (PrimitiveType::U128 | PrimitiveType::I128, true) => "__algoc_read_u128le",
                        _ => "__algoc_read_u32be",
                    };
                    self.write(&format!("{}(", read_fn));
                    self.generate_expr(expr);
                    self.write(")");
                    return;
                }

                // Integer to integer with different endianness - just cast
                let c_type = self.primitive_to_c(*p);
                self.write(&format!("({})(", c_type));
                self.generate_expr(expr);
                self.write(")");
                return;
            }
        }

        // Check for integer to byte array cast (e.g., value as u8[4])
        if let TypeKind::Array { element, size } = &ty.kind
            && let TypeKind::Primitive(PrimitiveType::U8) = &element.kind
        {
            // Get endianness from the source expression
            let (little_endian, bits) = self.get_expr_endianness_info(expr);

            let write_fn = match (bits, little_endian) {
                (16, false) => "__algoc_write_u16be",
                (16, true) => "__algoc_write_u16le",
                (32, false) => "__algoc_write_u32be",
                (32, true) => "__algoc_write_u32le",
                (64, false) => "__algoc_write_u64be",
                (64, true) => "__algoc_write_u64le",
                (128, false) => "__algoc_write_u128be",
                (128, true) => "__algoc_write_u128le",
                _ => "__algoc_write_u32be",
            };

            // Use a GCC statement expression to create a temp array
            self.write(&format!(
                "({{ uint8_t __tmp[{}]; memset(__tmp, 0, {}); {}(__tmp, ",
                size, size, write_fn
            ));

            // Unwrap any inner endian cast to get the raw value
            if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                self.generate_expr(inner);
            } else {
                self.generate_expr(expr);
            }
            self.write("); *(uint8_t(*)[");
            self.write(&format!("{}])__tmp; }})", size));
            return;
        }

        // Standard C casts
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let c_type = self.primitive_to_c(*p);
                self.write(&format!("({})(", c_type));
                self.generate_expr(expr);
                self.write(")");
            }
            _ => {
                // Other casts: try a C-style cast
                let c_type = self.type_to_c(ty);
                self.write(&format!("({})(", c_type));
                self.generate_expr(expr);
                self.write(")");
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

    /// Get the Reader method C function name for reading a field type
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

    /// Get the Writer method C function name for writing a field type
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

/// Check if an expression is a zero value
fn is_zero_value(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Integer(n) => *n == 0,
        ExprKind::Paren(inner) => is_zero_value(inner),
        _ => false,
    }
}

/// Escape a string for use in a C string literal
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

impl Default for CGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for CGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();
        self.func_signatures.clear();

        // Pre-pass: collect struct/layout definitions, method maps, and function signatures
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
                        methods.insert(method.name.name.clone(), mangled.clone());
                        // Also collect method signatures under mangled name
                        let params: Vec<FuncParamInfo> = method
                            .params
                            .iter()
                            .map(|p| FuncParamInfo {
                                needs_len: Self::param_needs_len(&p.ty),
                            })
                            .collect();
                        self.func_signatures.insert(mangled, params);
                    }
                    self.struct_methods
                        .insert(impl_def.target.name.clone(), methods);
                }
                ItemKind::Function(func) => {
                    let params: Vec<FuncParamInfo> = func
                        .params
                        .iter()
                        .map(|p| FuncParamInfo {
                            needs_len: Self::param_needs_len(&p.ty),
                        })
                        .collect();
                    self.func_signatures.insert(func.name.name.clone(), params);
                }
                _ => {}
            }
        }

        self.writeln("/* Generated by AlgoC */");
        self.writeln("/* DO NOT EDIT - This file is auto-generated */");
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

        // Generate test runner and main() if tests are included
        if self.include_tests {
            self.writeln("/* Test Runner */");
            self.writeln("int main(void) {");
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

            self.writeln("printf(\"\\n\");");
            self.writeln("printf(\"%d passed, %d failed\\n\", __passed, __failed);");
            self.writeln("return __failed == 0 ? 0 : 1;");
            self.dedent();
            self.writeln("}");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "c"
    }

    fn language_name(&self) -> &'static str {
        "C"
    }
}
