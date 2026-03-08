//! Kotlin code generator
//!
//! Generates Kotlin code from the analyzed AST.
//! Uses unsigned types (UByte, UInt, ULong, etc.) and handles bitwise operations
//! via infix functions (and, or, xor, shl, shr).

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

/// Kotlin code generator
pub struct KotlinGenerator {
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
    /// Variable element types for arrays/slices (for correct type conversion on assignment)
    var_elem_types: HashMap<String, PrimitiveType>,
}

impl KotlinGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            var_elem_types: HashMap::new(),
        }
    }

    /// Set whether to include tests in the output
    pub fn with_tests(mut self, include: bool) -> Self {
        self.include_tests = include;
        self
    }

    /// Extract the element primitive type from array/slice/ref types
    fn element_primitive(ty: &ParserType) -> Option<PrimitiveType> {
        match &ty.kind {
            crate::parser::TypeKind::Array { element, .. }
            | crate::parser::TypeKind::Slice { element }
            | crate::parser::TypeKind::ArrayRef { element, .. } => {
                if let crate::parser::TypeKind::Primitive(p) = &element.kind {
                    Some(*p)
                } else {
                    None
                }
            }
            crate::parser::TypeKind::MutRef(inner) | crate::parser::TypeKind::Ref(inner) => {
                Self::element_primitive(inner)
            }
            _ => None,
        }
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

        // Reader class
        self.writeln("@OptIn(ExperimentalUnsignedTypes::class)");
        self.writeln("class Reader(data: UByteArray) {");
        self.indent();
        self.writeln("private val data: UByteArray = data");
        self.writeln("var pos: Int = 0");
        self.writeln("");

        // read_u8
        self.writeln("fun read_u8(): UByte {");
        self.indent();
        self.writeln("if (pos >= data.size) throw Exception(\"EOF\")");
        self.writeln("return data[pos++]");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u16be
        self.writeln("fun read_u16(): UShort = read_u16be()");
        self.writeln("fun read_u16be(): UShort {");
        self.indent();
        self.writeln("if (pos + 2 > data.size) throw Exception(\"EOF\")");
        self.writeln("val v = ((data[pos].toUInt() shl 8) or data[pos + 1].toUInt()).toUShort()");
        self.writeln("pos += 2");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("fun read_u16le(): UShort {");
        self.indent();
        self.writeln("if (pos + 2 > data.size) throw Exception(\"EOF\")");
        self.writeln("val v = (data[pos].toUInt() or (data[pos + 1].toUInt() shl 8)).toUShort()");
        self.writeln("pos += 2");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u32
        self.writeln("fun read_u32(): UInt = read_u32be()");
        self.writeln("fun read_u32be(): UInt {");
        self.indent();
        self.writeln("if (pos + 4 > data.size) throw Exception(\"EOF\")");
        self.writeln("val v = (data[pos].toUInt() shl 24) or (data[pos + 1].toUInt() shl 16) or (data[pos + 2].toUInt() shl 8) or data[pos + 3].toUInt()");
        self.writeln("pos += 4");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("fun read_u32le(): UInt {");
        self.indent();
        self.writeln("if (pos + 4 > data.size) throw Exception(\"EOF\")");
        self.writeln("val v = data[pos].toUInt() or (data[pos + 1].toUInt() shl 8) or (data[pos + 2].toUInt() shl 16) or (data[pos + 3].toUInt() shl 24)");
        self.writeln("pos += 4");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u64
        self.writeln("fun read_u64(): ULong = read_u64be()");
        self.writeln("fun read_u64be(): ULong {");
        self.indent();
        self.writeln("if (pos + 8 > data.size) throw Exception(\"EOF\")");
        self.writeln("val v = (data[pos].toULong() shl 56) or (data[pos + 1].toULong() shl 48) or (data[pos + 2].toULong() shl 40) or (data[pos + 3].toULong() shl 32) or (data[pos + 4].toULong() shl 24) or (data[pos + 5].toULong() shl 16) or (data[pos + 6].toULong() shl 8) or data[pos + 7].toULong()");
        self.writeln("pos += 8");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("fun read_u64le(): ULong {");
        self.indent();
        self.writeln("if (pos + 8 > data.size) throw Exception(\"EOF\")");
        self.writeln("val v = data[pos].toULong() or (data[pos + 1].toULong() shl 8) or (data[pos + 2].toULong() shl 16) or (data[pos + 3].toULong() shl 24) or (data[pos + 4].toULong() shl 32) or (data[pos + 5].toULong() shl 40) or (data[pos + 6].toULong() shl 48) or (data[pos + 7].toULong() shl 56)");
        self.writeln("pos += 8");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_bytes
        self.writeln("fun read_bytes(count: Int): UByteArray {");
        self.indent();
        self.writeln("if (pos + count > data.size) throw Exception(\"EOF\")");
        self.writeln("val result = data.copyOfRange(pos, pos + count)");
        self.writeln("pos += count");
        self.writeln("return result");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_chunk
        self.writeln("fun read_chunk(maxSize: Int): UByteArray {");
        self.indent();
        self.writeln("val remaining = data.size - pos");
        self.writeln("val count = minOf(maxSize, remaining)");
        self.writeln("val result = data.copyOfRange(pos, pos + count)");
        self.writeln("pos += count");
        self.writeln("return result");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // eof
        self.writeln("fun eof(): Boolean = pos >= data.size");

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer class
        self.writeln("@OptIn(ExperimentalUnsignedTypes::class)");
        self.writeln("class Writer(data: UByteArray) {");
        self.indent();
        self.writeln("private val data: UByteArray = data");
        self.writeln("var pos: Int = 0");
        self.writeln("");

        // write_u8
        self.writeln("fun write_u8(v: UByte) {");
        self.indent();
        self.writeln("if (pos >= data.size) throw Exception(\"Buffer overflow\")");
        self.writeln("data[pos++] = v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u16
        self.writeln("fun write_u16(v: UShort) = write_u16be(v)");
        self.writeln("fun write_u16be(v: UShort) {");
        self.indent();
        self.writeln("if (pos + 2 > data.size) throw Exception(\"Buffer overflow\")");
        self.writeln("data[pos] = (v.toUInt() shr 8).toUByte()");
        self.writeln("data[pos + 1] = (v.toUInt() and 0xFFu).toUByte()");
        self.writeln("pos += 2");
        self.dedent();
        self.writeln("}");
        self.writeln("fun write_u16le(v: UShort) {");
        self.indent();
        self.writeln("if (pos + 2 > data.size) throw Exception(\"Buffer overflow\")");
        self.writeln("data[pos] = (v.toUInt() and 0xFFu).toUByte()");
        self.writeln("data[pos + 1] = (v.toUInt() shr 8).toUByte()");
        self.writeln("pos += 2");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u32
        self.writeln("fun write_u32(v: UInt) = write_u32be(v)");
        self.writeln("fun write_u32be(v: UInt) {");
        self.indent();
        self.writeln("if (pos + 4 > data.size) throw Exception(\"Buffer overflow\")");
        self.writeln("data[pos] = (v shr 24).toUByte()");
        self.writeln("data[pos + 1] = ((v shr 16) and 0xFFu).toUByte()");
        self.writeln("data[pos + 2] = ((v shr 8) and 0xFFu).toUByte()");
        self.writeln("data[pos + 3] = (v and 0xFFu).toUByte()");
        self.writeln("pos += 4");
        self.dedent();
        self.writeln("}");
        self.writeln("fun write_u32le(v: UInt) {");
        self.indent();
        self.writeln("if (pos + 4 > data.size) throw Exception(\"Buffer overflow\")");
        self.writeln("data[pos] = (v and 0xFFu).toUByte()");
        self.writeln("data[pos + 1] = ((v shr 8) and 0xFFu).toUByte()");
        self.writeln("data[pos + 2] = ((v shr 16) and 0xFFu).toUByte()");
        self.writeln("data[pos + 3] = (v shr 24).toUByte()");
        self.writeln("pos += 4");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u64
        self.writeln("fun write_u64(v: ULong) = write_u64be(v)");
        self.writeln("fun write_u64be(v: ULong) {");
        self.indent();
        self.writeln("if (pos + 8 > data.size) throw Exception(\"Buffer overflow\")");
        for i in 0..8 {
            let shift = (7 - i) * 8;
            if shift > 0 {
                self.writeln(&format!(
                    "data[pos + {}] = ((v shr {}) and 0xFFu).toUByte()",
                    i, shift
                ));
            } else {
                self.writeln(&format!("data[pos + {}] = (v and 0xFFu).toUByte()", i));
            }
        }
        self.writeln("pos += 8");
        self.dedent();
        self.writeln("}");
        self.writeln("fun write_u64le(v: ULong) {");
        self.indent();
        self.writeln("if (pos + 8 > data.size) throw Exception(\"Buffer overflow\")");
        for i in 0..8 {
            let shift = i * 8;
            if shift > 0 {
                self.writeln(&format!(
                    "data[pos + {}] = ((v shr {}) and 0xFFu).toUByte()",
                    i, shift
                ));
            } else {
                self.writeln(&format!("data[pos + {}] = (v and 0xFFu).toUByte()", i));
            }
        }
        self.writeln("pos += 8");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_bytes
        self.writeln("fun write_bytes(src: UByteArray) {");
        self.indent();
        self.writeln("if (pos + src.size > data.size) throw Exception(\"Buffer overflow\")");
        self.writeln("src.copyInto(data, pos)");
        self.writeln("pos += src.size");
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
        self.writeln("var __test_failures = 0");
        self.writeln("var __test_name = \"\"");
        self.writeln("");
        self.writeln("fun __assert(condition: Boolean) {");
        self.indent();
        self.writeln("if (!condition) {");
        self.indent();
        self.writeln("__test_failures++");
        self.writeln("println(\"  ASSERTION FAILED in $__test_name\")");
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
        let saved_elem_types = self.var_elem_types.clone();
        for param in &func.params {
            if let Some(elem_prim) = Self::element_primitive(&param.ty) {
                self.var_elem_types
                    .insert(param.name.name.clone(), elem_prim);
            }
        }

        let mangled_name = format!("{}__{}", struct_name, func.name.name);
        let mut params: Vec<String> = Vec::new();
        for param in &func.params {
            let ty_str = self.type_to_kotlin(&param.ty);
            params.push(format!("{}: {}", param.name.name, ty_str));
        }

        self.writeln(&format!(
            "fun {}({}){} {{",
            mangled_name,
            params.join(", "),
            self.return_type_str(func.return_type.as_ref()),
        ));
        self.indent();
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.var_elem_types = saved_elem_types;
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("fun test_{}() {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        self.write(&format!("val {} = ", c.name.name));
        self.generate_expr(&c.value);
        self.write("\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Generate a data class for the struct
        self.write_indent();
        self.write(&format!("data class {}(\n", s.name.name));
        self.indent();
        for (i, field) in s.fields.iter().enumerate() {
            let comma = if i < s.fields.len() - 1 { "," } else { "" };
            let ty_str = self.type_to_kotlin(&field.ty);
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!(
                "var {}: {} = {}{}",
                field.name.name, ty_str, init, comma
            ));
        }
        self.dedent();
        self.writeln(")");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are like structs
        self.write_indent();
        self.write(&format!("data class {}(\n", l.name.name));
        self.indent();
        for (i, field) in l.fields.iter().enumerate() {
            let comma = if i < l.fields.len() - 1 { "," } else { "" };
            let ty_str = self.type_to_kotlin(&field.ty);
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!(
                "var {}: {} = {}{}",
                field.name.name, ty_str, init, comma
            ));
        }
        self.dedent();
        self.writeln(")");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum as a sealed class hierarchy
        self.writeln(&format!("sealed class {} {{", e.name.name));
        self.indent();

        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!("object {} : {}()", variant.name.name, e.name.name));
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    let params: Vec<String> = types
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| format!("val v{}: {}", i, self.type_to_kotlin(ty)))
                        .collect();
                    self.writeln(&format!(
                        "data class {}({}) : {}()",
                        variant.name.name,
                        params.join(", "),
                        e.name.name,
                    ));
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    let params: Vec<String> = fields
                        .iter()
                        .map(|f| format!("val {}: {}", f.name.name, self.type_to_kotlin(&f.ty)))
                        .collect();
                    self.writeln(&format!(
                        "data class {}({}) : {}()",
                        variant.name.name,
                        params.join(", "),
                        e.name.name,
                    ));
                }
            }
        }

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Map a parser Type to Kotlin type string
    #[allow(clippy::only_used_in_recursion)]
    fn type_to_kotlin(&self, ty: &ParserType) -> String {
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => "UByte".to_string(),
                    PrimitiveType::U16 | PrimitiveType::I16 => "UShort".to_string(),
                    PrimitiveType::U32 | PrimitiveType::I32 => "UInt".to_string(),
                    PrimitiveType::U64 | PrimitiveType::I64 => "ULong".to_string(),
                    PrimitiveType::U128 | PrimitiveType::I128 => "ULong".to_string(), // best we can do natively
                    PrimitiveType::Bool => "Boolean".to_string(),
                    // Endian types map to their native equivalent
                    _ => "UInt".to_string(),
                }
            }
            TypeKind::Array { element, size } => {
                let elem_str = self.type_to_kotlin(element);
                match elem_str.as_str() {
                    "UByte" => format!("UByteArray /* {} */", size),
                    "UShort" => format!("UShortArray /* {} */", size),
                    "UInt" => format!("UIntArray /* {} */", size),
                    "ULong" => format!("ULongArray /* {} */", size),
                    _ => format!("Array<{}> /* {} */", elem_str, size),
                }
            }
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                let elem_str = self.type_to_kotlin(element);
                match elem_str.as_str() {
                    "UByte" => "UByteArray".to_string(),
                    "UShort" => "UShortArray".to_string(),
                    "UInt" => "UIntArray".to_string(),
                    "ULong" => "ULongArray".to_string(),
                    _ => format!("Array<{}>", elem_str),
                }
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.type_to_kotlin(inner),
            TypeKind::Named(ident) => ident.name.clone(),
            TypeKind::SelfType => "Any".to_string(), // placeholder
        }
    }

    /// Get the return type string for a function (": Type" or empty string)
    fn return_type_str(&self, ret_type: Option<&ParserType>) -> String {
        match ret_type {
            Some(ty) => format!(": {}", self.type_to_kotlin(ty)),
            None => String::new(),
        }
    }

    fn default_value_for_type(&self, ty: &ParserType) -> String {
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => "0u.toUByte()".to_string(),
                    PrimitiveType::U16 | PrimitiveType::I16 => "0u.toUShort()".to_string(),
                    PrimitiveType::U32 | PrimitiveType::I32 => "0u".to_string(),
                    PrimitiveType::U64 | PrimitiveType::I64 => "0uL".to_string(),
                    PrimitiveType::U128 | PrimitiveType::I128 => "0uL".to_string(),
                    PrimitiveType::Bool => "false".to_string(),
                    _ => "0u".to_string(),
                }
            }
            TypeKind::Array { element, size } => {
                let elem_str = self.type_to_kotlin(element);
                match elem_str.as_str() {
                    "UByte" => format!("UByteArray({})", size),
                    "UShort" => format!("UShortArray({})", size),
                    "UInt" => format!("UIntArray({})", size),
                    "ULong" => format!("ULongArray({})", size),
                    _ => format!(
                        "Array({}) {{ {} }}",
                        size,
                        self.default_value_for_type(element)
                    ),
                }
            }
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                let elem_str = self.type_to_kotlin(element);
                match elem_str.as_str() {
                    "UByte" => "UByteArray(0)".to_string(),
                    "UShort" => "UShortArray(0)".to_string(),
                    "UInt" => "UIntArray(0)".to_string(),
                    "ULong" => "ULongArray(0)".to_string(),
                    _ => format!("emptyArray<{}>()", elem_str),
                }
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.default_value_for_type(inner),
            TypeKind::Named(ident) => {
                format!("{}()", ident.name)
            }
            _ => "0u".to_string(),
        }
    }

    /// Check if an assignment target is a UByte-typed location that needs .toUByte() conversion
    fn target_needs_ubyte_conversion(&self, target: &Expr) -> bool {
        match &target.kind {
            ExprKind::Index { array, .. } => {
                // Check if the array element type is UByte
                if let ExprKind::Ident(ident) = &array.kind
                    && let Some(elem_prim) = self.var_elem_types.get(&ident.name)
                {
                    return matches!(elem_prim.to_native(), PrimitiveType::U8 | PrimitiveType::I8);
                }
                if let ExprKind::Field { object, field } = &array.kind
                    && let ExprKind::Ident(obj_ident) = &object.kind
                    && let Some(struct_name) = self.var_types.get(&obj_ident.name)
                    && let Some(fields) = self.struct_defs.get(struct_name)
                {
                    for f in fields {
                        if f.name == field.name
                            && let Some(elem_prim) = Self::element_primitive(&f.ty)
                        {
                            return matches!(
                                elem_prim.to_native(),
                                PrimitiveType::U8 | PrimitiveType::I8
                            );
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    fn generate_function(&mut self, func: &Function) {
        // Track parameter element types for correct type conversion
        let saved_elem_types = self.var_elem_types.clone();
        for param in &func.params {
            if let Some(elem_prim) = Self::element_primitive(&param.ty) {
                self.var_elem_types
                    .insert(param.name.name.clone(), elem_prim);
            }
        }

        self.write_indent();

        // Build parameter list
        let mut params: Vec<String> = Vec::new();
        for param in &func.params {
            let ty_str = self.type_to_kotlin(&param.ty);
            params.push(format!("{}: {}", param.name.name, ty_str));
        }

        self.write(&format!(
            "fun {}({}){} {{\n",
            func.name.name,
            params.join(", "),
            self.return_type_str(func.return_type.as_ref()),
        ));
        self.indent();

        self.generate_block(&func.body);

        self.dedent();
        self.writeln("}");
        self.writeln("");
        self.var_elem_types = saved_elem_types;
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

                // Track element types for arrays/slices
                if let Some(ty) = ty
                    && let Some(elem_prim) = Self::element_primitive(ty)
                {
                    self.var_elem_types.insert(name.name.clone(), elem_prim);
                }

                // Infer element type from ArrayRepeat with cast
                if let Some(init_expr) = init
                    && let ExprKind::ArrayRepeat { value, .. } = &init_expr.kind
                    && let ExprKind::Cast { ty, .. } = &value.kind
                    && let crate::parser::TypeKind::Primitive(p) = &ty.kind
                {
                    self.var_elem_types.insert(name.name.clone(), *p);
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
                let kw = if *mutable { "var" } else { "val" };

                if let Some(ty) = ty {
                    let ty_str = self.type_to_kotlin(ty);
                    self.write(&format!("{} {}: {}", kw, name.name, ty_str));
                } else {
                    self.write(&format!("{} {}", kw, name.name));
                }

                if let Some(init) = init {
                    self.write(" = ");
                    self.generate_expr(init);
                } else if let Some(ty) = ty {
                    self.write(&format!(" = {}", self.default_value_for_type(ty)));
                }
                self.write("\n");
            }
            StmtKind::Expr(expr) => {
                self.write_indent();
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
                        self.generate_endian_write_to_slice(array, start, end, p, value);
                        return;
                    }
                }

                // Check if assigning to an index of a UByteArray - needs .toUByte()
                let needs_to_ubyte = self.target_needs_ubyte_conversion(target);

                self.write_indent();
                self.generate_expr(target);
                self.write(" = ");
                if needs_to_ubyte {
                    self.write("(");
                    self.generate_expr(value);
                    self.write(").toUByte()");
                } else {
                    self.generate_expr(value);
                }
                self.write("\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                self.write_indent();
                // Kotlin unsigned types don't support compound assignment with
                // bitwise ops directly using +=. We have to expand them.
                match op {
                    BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::Shl
                    | BinaryOp::Shr => {
                        // target = target op value
                        self.generate_expr(target);
                        self.write(" = ");
                        self.generate_expr(target);
                        let op_str = match op {
                            BinaryOp::BitAnd => " and ",
                            BinaryOp::BitOr => " or ",
                            BinaryOp::BitXor => " xor ",
                            BinaryOp::Shl => " shl ",
                            BinaryOp::Shr => " shr ",
                            _ => unreachable!(),
                        };
                        self.write(op_str);
                        // shl/shr need Int operand
                        if matches!(op, BinaryOp::Shl | BinaryOp::Shr) {
                            self.generate_shift_amount(value);
                        } else {
                            self.generate_expr(value);
                        }
                        self.write("\n");
                    }
                    _ => {
                        let op_str = match op {
                            BinaryOp::Add => "+=",
                            BinaryOp::Sub => "-=",
                            BinaryOp::Mul => "*=",
                            BinaryOp::Div => "/=",
                            BinaryOp::Rem => "%=",
                            _ => "=",
                        };
                        self.generate_expr(target);
                        self.write(&format!(" {} ", op_str));
                        self.generate_expr(value);
                        self.write("\n");
                    }
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
                let range_op = if *inclusive { ".." } else { " until " };
                self.write(&format!("for ({} in ", var.name));
                self.generate_expr_as_int(start);
                self.write(range_op);
                self.generate_expr_as_int(end);
                self.write(") {\n");
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
                self.writeln("run {");
                self.indent();
                self.generate_block(block);
                self.dedent();
                self.writeln("}");
            }
        }
    }

    /// Generate an expression, ensuring it is an Int (for Kotlin range bounds, shift amounts, etc.)
    fn generate_expr_as_int(&mut self, expr: &Expr) {
        // For integer literals, just output directly
        if let ExprKind::Integer(n) = &expr.kind {
            self.write(&format!("{}", n));
            return;
        }
        // Otherwise wrap with .toInt()
        self.write("(");
        self.generate_expr(expr);
        self.write(").toInt()");
    }

    /// Generate a shift amount expression. Kotlin requires shift amount to be Int.
    fn generate_shift_amount(&mut self, expr: &Expr) {
        if let ExprKind::Integer(n) = &expr.kind {
            self.write(&format!("{}", n));
            return;
        }
        self.write("(");
        self.generate_expr(expr);
        self.write(").toInt()");
    }

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                // Kotlin unsigned literals
                if *n <= u32::MAX as u128 {
                    self.write(&format!("{}u", n));
                } else if *n <= u64::MAX as u128 {
                    self.write(&format!("{}uL", n));
                } else {
                    // u128 - use ULong with masking (lossy for >64 bits)
                    self.write(&format!("{}uL", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // Convert string to UByteArray
                self.write(&format!(
                    "\"{}\".toByteArray().toUByteArray()",
                    escape_kotlin_string(s)
                ));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!(
                    "\"{}\".toByteArray().toUByteArray()",
                    escape_kotlin_string(s)
                ));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to UByteArray
                if h.is_empty() {
                    self.write("UByteArray(0)");
                } else {
                    self.write("ubyteArrayOf(");
                    let bytes: Vec<String> = h
                        .as_bytes()
                        .chunks(2)
                        .map(|chunk| {
                            let s = std::str::from_utf8(chunk).unwrap_or("00");
                            format!("0x{}u", s)
                        })
                        .collect();
                    self.write(&bytes.join(", "));
                    self.write(")");
                }
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                // For array comparisons, use contentEquals
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

                // Kotlin uses infix functions for bitwise operations on unsigned types
                match op {
                    BinaryOp::BitAnd => {
                        self.write("(");
                        self.generate_expr(left);
                        self.write(" and ");
                        self.generate_expr(right);
                        self.write(")");
                    }
                    BinaryOp::BitOr => {
                        self.write("(");
                        self.generate_expr(left);
                        self.write(" or ");
                        self.generate_expr(right);
                        self.write(")");
                    }
                    BinaryOp::BitXor => {
                        self.write("(");
                        self.generate_expr(left);
                        self.write(" xor ");
                        self.generate_expr(right);
                        self.write(")");
                    }
                    BinaryOp::Shl => {
                        self.write("(");
                        self.generate_expr(left);
                        self.write(" shl ");
                        self.generate_shift_amount(right);
                        self.write(")");
                    }
                    BinaryOp::Shr => {
                        self.write("(");
                        self.generate_expr(left);
                        self.write(" shr ");
                        self.generate_shift_amount(right);
                        self.write(")");
                    }
                    BinaryOp::And => {
                        self.write("(");
                        self.generate_expr(left);
                        self.write(" && ");
                        self.generate_expr(right);
                        self.write(")");
                    }
                    BinaryOp::Or => {
                        self.write("(");
                        self.generate_expr(left);
                        self.write(" || ");
                        self.generate_expr(right);
                        self.write(")");
                    }
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge => {
                        let op_str = match op {
                            BinaryOp::Eq => " == ",
                            BinaryOp::Ne => " != ",
                            BinaryOp::Lt => " < ",
                            BinaryOp::Le => " <= ",
                            BinaryOp::Gt => " > ",
                            BinaryOp::Ge => " >= ",
                            _ => unreachable!(),
                        };
                        // Kotlin unsigned types (UByte, UShort, UInt, ULong) cannot
                        // be compared across types. Convert both sides to ULong to
                        // ensure compatible types, unless either side is boolean.
                        let needs_cast = !is_bool_like_expr(left) && !is_bool_like_expr(right);
                        self.write("(");
                        self.generate_expr(left);
                        if needs_cast {
                            self.write(".toULong()");
                        }
                        self.write(op_str);
                        self.generate_expr(right);
                        if needs_cast {
                            self.write(".toULong()");
                        }
                        self.write(")");
                    }
                    _ => {
                        let op_str = match op {
                            BinaryOp::Add => " + ",
                            BinaryOp::Sub => " - ",
                            BinaryOp::Mul => " * ",
                            BinaryOp::Div => " / ",
                            BinaryOp::Rem => " % ",
                            _ => unreachable!(),
                        };
                        self.write("(");
                        self.generate_expr(left);
                        self.write(op_str);
                        self.generate_expr(right);
                        self.write(")");
                    }
                }
            }
            ExprKind::Unary { op, operand } => match op {
                UnaryOp::Neg => {
                    // Kotlin unsigned types don't support unary minus
                    // We need to negate via two's complement or cast
                    self.write("(-(");
                    self.generate_expr(operand);
                    self.write(").toInt()).toUInt()");
                }
                UnaryOp::Not => {
                    self.write("!(");
                    self.generate_expr(operand);
                    self.write(")");
                }
                UnaryOp::BitNot => {
                    self.generate_expr(operand);
                    self.write(".inv()");
                }
            },
            ExprKind::Index { array, index } => {
                self.generate_expr(array);
                self.write("[");
                self.generate_expr_as_int(index);
                self.write("]");
            }
            ExprKind::Slice {
                array,
                start,
                end,
                inclusive,
            } => {
                self.generate_expr(array);
                self.write(".copyOfRange(");
                self.generate_expr_as_int(start);
                self.write(", ");
                if *inclusive {
                    self.write("(");
                    self.generate_expr_as_int(end);
                    self.write(") + 1");
                } else {
                    self.generate_expr_as_int(end);
                }
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
                        // Convert .len() to .size
                        self.generate_expr(object);
                        self.write(".size");
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
                        self.write("run { ");
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
                            self.write("run { ");
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

                    // Reader/Writer method calls - pass through
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
                    self.write("ubyteArrayOf()");
                } else {
                    // Check if all elements are small integers (bytes)
                    let all_bytes = elements.iter().all(|e| {
                        if let ExprKind::Integer(n) = &e.kind {
                            *n <= 255
                        } else {
                            false
                        }
                    });
                    let all_ints = elements
                        .iter()
                        .all(|e| matches!(e.kind, ExprKind::Integer(_)));

                    if all_bytes {
                        self.write("ubyteArrayOf(");
                    } else if all_ints {
                        self.write("uintArrayOf(");
                    } else {
                        self.write("arrayOf(");
                    }
                    for (i, elem) in elements.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(elem);
                    }
                    self.write(")");
                }
            }
            ExprKind::ArrayRepeat { value, count } => {
                let is_byte = is_byte_value(value);
                if is_byte {
                    self.write("UByteArray(");
                    self.generate_expr_as_int(count);
                    self.write(") { ");
                    self.generate_expr(value);
                    self.write(".toUByte() }");
                } else {
                    self.write("UIntArray(");
                    self.generate_expr_as_int(count);
                    self.write(") { ");
                    self.generate_expr(value);
                    self.write(" }");
                }
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in Kotlin are just the value (pass by reference for objects)
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are no-ops
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
                self.write(&format!("{}(", name.name));
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("{} = ", field_name.name));
                    self.generate_expr(value);
                }
                self.write(")");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // Kotlin: if (cond) then_val else else_val (expression)
                self.write("(if (");
                self.generate_expr(condition);
                self.write(") ");
                self.generate_expr(then_expr);
                self.write(" else ");
                self.generate_expr(else_expr);
                self.write(")");
            }
            ExprKind::EnumVariant {
                enum_name,
                variant_name,
                args,
            } => {
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
                // Generate as Kotlin `when` expression
                self.write("when (");
                self.generate_expr(expr);
                self.write(") {\n");
                self.indent();
                for arm in arms {
                    self.write_indent();
                    self.generate_when_pattern(&arm.pattern);
                    self.write(" -> ");
                    self.generate_expr(&arm.body);
                    self.write("\n");
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

    fn generate_when_pattern(&mut self, pattern: &crate::parser::Pattern) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("else");
            }
            PatternKind::Literal(lit_expr) => {
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(_ident) => {
                // Binding pattern - use else (catch-all)
                self.write("else");
            }
            PatternKind::EnumVariant {
                enum_name,
                variant_name,
                ..
            } => {
                self.write(&format!("is {}.{}", enum_name.name, variant_name.name));
            }
            PatternKind::Tuple(_patterns) => {
                self.write("else");
            }
            PatternKind::Or(patterns) => {
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_when_pattern(p);
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
                    Endianness::Native => "be",
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

                // Check if source is a byte sequence (endian conversion from bytes)
                if is_byte_sequence_expr(expr) {
                    self.generate_bytes_to_int(expr, native, little_endian);
                    return;
                }

                // Integer to integer with different endianness - just mask
                match native {
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        self.write("(");
                        self.generate_expr(expr);
                        self.write(").toUShort()");
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        self.write("(");
                        self.generate_expr(expr);
                        self.write(").toUInt()");
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        self.write("(");
                        self.generate_expr(expr);
                        self.write(").toULong()");
                    }
                    _ => {
                        self.generate_expr(expr);
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
            self.generate_int_to_bytes(expr, *size, bits, little_endian);
            return;
        }

        // Standard casts - map to Kotlin conversion functions
        match &ty.kind {
            TypeKind::Primitive(p) => match p {
                PrimitiveType::U8 | PrimitiveType::I8 => {
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(").toUByte()");
                }
                PrimitiveType::U16 | PrimitiveType::I16 => {
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(").toUShort()");
                }
                PrimitiveType::U32 | PrimitiveType::I32 => {
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(").toUInt()");
                }
                PrimitiveType::U64 | PrimitiveType::I64 => {
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(").toULong()");
                }
                PrimitiveType::U128 | PrimitiveType::I128 => {
                    // Best effort with ULong
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(").toULong()");
                }
                PrimitiveType::Bool => {
                    self.write("((");
                    self.generate_expr(expr);
                    self.write(") != 0u)");
                }
                // Endian types with Native endianness (shouldn't happen, but handle)
                _ => {
                    self.generate_expr(expr);
                }
            },
            _ => {
                self.generate_expr(expr);
            }
        }
    }

    /// Generate code to convert a byte sequence to an integer with endianness
    fn generate_bytes_to_int(
        &mut self,
        expr: &Expr,
        native: crate::parser::PrimitiveType,
        little_endian: bool,
    ) {
        use crate::parser::PrimitiveType;

        self.write("run { val __b = ");
        self.generate_expr(expr);
        self.write("; ");

        match native {
            PrimitiveType::U16 | PrimitiveType::I16 => {
                if little_endian {
                    self.write("(__b[0].toUInt() or (__b[1].toUInt() shl 8)).toUShort()");
                } else {
                    self.write("((__b[0].toUInt() shl 8) or __b[1].toUInt()).toUShort()");
                }
            }
            PrimitiveType::U32 | PrimitiveType::I32 => {
                if little_endian {
                    self.write("__b[0].toUInt() or (__b[1].toUInt() shl 8) or (__b[2].toUInt() shl 16) or (__b[3].toUInt() shl 24)");
                } else {
                    self.write("(__b[0].toUInt() shl 24) or (__b[1].toUInt() shl 16) or (__b[2].toUInt() shl 8) or __b[3].toUInt()");
                }
            }
            PrimitiveType::U64 | PrimitiveType::I64 => {
                if little_endian {
                    self.write("__b[0].toULong() or (__b[1].toULong() shl 8) or (__b[2].toULong() shl 16) or (__b[3].toULong() shl 24) or (__b[4].toULong() shl 32) or (__b[5].toULong() shl 40) or (__b[6].toULong() shl 48) or (__b[7].toULong() shl 56)");
                } else {
                    self.write("(__b[0].toULong() shl 56) or (__b[1].toULong() shl 48) or (__b[2].toULong() shl 40) or (__b[3].toULong() shl 32) or (__b[4].toULong() shl 24) or (__b[5].toULong() shl 16) or (__b[6].toULong() shl 8) or __b[7].toULong()");
                }
            }
            PrimitiveType::U128 | PrimitiveType::I128 => {
                // Use ULong for 128-bit (lossy for >64 bits; best-effort)
                if little_endian {
                    self.write("__b[0].toULong() or (__b[1].toULong() shl 8) or (__b[2].toULong() shl 16) or (__b[3].toULong() shl 24) or (__b[4].toULong() shl 32) or (__b[5].toULong() shl 40) or (__b[6].toULong() shl 48) or (__b[7].toULong() shl 56)");
                } else {
                    self.write("(__b[8].toULong() shl 56) or (__b[9].toULong() shl 48) or (__b[10].toULong() shl 40) or (__b[11].toULong() shl 32) or (__b[12].toULong() shl 24) or (__b[13].toULong() shl 16) or (__b[14].toULong() shl 8) or __b[15].toULong()");
                }
            }
            _ => {
                // Fallback: treat as u32
                if little_endian {
                    self.write("__b[0].toUInt() or (__b[1].toUInt() shl 8) or (__b[2].toUInt() shl 16) or (__b[3].toUInt() shl 24)");
                } else {
                    self.write("(__b[0].toUInt() shl 24) or (__b[1].toUInt() shl 16) or (__b[2].toUInt() shl 8) or __b[3].toUInt()");
                }
            }
        }

        self.write(" }");
    }

    /// Generate code to convert an integer to a byte array with endianness
    fn generate_int_to_bytes(&mut self, expr: &Expr, size: u64, bits: u32, little_endian: bool) {
        let inner_expr = if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
            inner
        } else {
            expr
        };

        self.write("run { val __v = (");
        self.generate_expr(inner_expr);

        if bits <= 32 {
            self.write(").toUInt(); val __a = UByteArray(");
            self.write(&format!("{})", size));
            if little_endian {
                for i in 0..size.min(4) {
                    let shift = i * 8;
                    if shift > 0 {
                        self.write(&format!(
                            "; __a[{}] = ((__v shr {}) and 0xFFu).toUByte()",
                            i, shift
                        ));
                    } else {
                        self.write(&format!("; __a[{}] = (__v and 0xFFu).toUByte()", i));
                    }
                }
            } else {
                let byte_count = size.min(4);
                for i in 0..byte_count {
                    let shift = (byte_count - 1 - i) * 8;
                    if shift > 0 {
                        self.write(&format!(
                            "; __a[{}] = ((__v shr {}) and 0xFFu).toUByte()",
                            i, shift
                        ));
                    } else {
                        self.write(&format!("; __a[{}] = (__v and 0xFFu).toUByte()", i));
                    }
                }
            }
        } else if bits <= 64 {
            self.write(").toULong(); val __a = UByteArray(");
            self.write(&format!("{})", size));
            if little_endian {
                for i in 0..size.min(8) {
                    let shift = i * 8;
                    if shift > 0 {
                        self.write(&format!(
                            "; __a[{}] = ((__v shr {}) and 0xFFuL).toUByte()",
                            i, shift
                        ));
                    } else {
                        self.write(&format!("; __a[{}] = (__v and 0xFFuL).toUByte()", i));
                    }
                }
            } else {
                let byte_count = size.min(8);
                for i in 0..byte_count {
                    let shift = (byte_count - 1 - i) * 8;
                    if shift > 0 {
                        self.write(&format!(
                            "; __a[{}] = ((__v shr {}) and 0xFFuL).toUByte()",
                            i, shift
                        ));
                    } else {
                        self.write(&format!("; __a[{}] = (__v and 0xFFuL).toUByte()", i));
                    }
                }
            }
        } else {
            // 128-bit: best-effort using ULong
            self.write(").toULong(); val __a = UByteArray(");
            self.write(&format!("{})", size));
            if little_endian {
                for i in 0..size.min(16) {
                    let shift = i * 8;
                    if shift > 0 && shift < 64 {
                        self.write(&format!(
                            "; __a[{}] = ((__v shr {}) and 0xFFuL).toUByte()",
                            i, shift
                        ));
                    } else if shift == 0 {
                        self.write(&format!("; __a[{}] = (__v and 0xFFuL).toUByte()", i));
                    } else {
                        self.write(&format!("; __a[{}] = 0u.toUByte()", i));
                    }
                }
            } else {
                for i in 0..size.min(16) {
                    let shift_from_right = (size.min(16) - 1 - i) * 8;
                    if shift_from_right > 0 && shift_from_right < 64 {
                        self.write(&format!(
                            "; __a[{}] = ((__v shr {}) and 0xFFuL).toUByte()",
                            i, shift_from_right
                        ));
                    } else if shift_from_right == 0 {
                        self.write(&format!("; __a[{}] = (__v and 0xFFuL).toUByte()", i));
                    } else {
                        self.write(&format!("; __a[{}] = 0u.toUByte()", i));
                    }
                }
            }
        }

        self.write("; __a }");
    }

    /// Generate endian write to a slice: buf[start..end] as u32be = value
    fn generate_endian_write_to_slice(
        &mut self,
        array: &Expr,
        start: &Expr,
        _end: &Expr,
        p: &crate::parser::PrimitiveType,
        value: &Expr,
    ) {
        use crate::parser::PrimitiveType;
        let endian = p.endianness();
        let little_endian = endian == crate::parser::Endianness::Little;
        let native = p.to_native();

        self.write_indent();
        self.write("run { val __s = ");
        self.generate_expr_as_int(start);
        self.write("; val __arr = ");
        self.generate_expr(array);
        self.write("; val __v = (");
        self.generate_expr(value);

        match native {
            PrimitiveType::U16 | PrimitiveType::I16 => {
                self.write(").toUInt()");
                if little_endian {
                    self.write("; __arr[__s] = (__v and 0xFFu).toUByte()");
                    self.write("; __arr[__s + 1] = ((__v shr 8) and 0xFFu).toUByte()");
                } else {
                    self.write("; __arr[__s] = ((__v shr 8) and 0xFFu).toUByte()");
                    self.write("; __arr[__s + 1] = (__v and 0xFFu).toUByte()");
                }
            }
            PrimitiveType::U32 | PrimitiveType::I32 => {
                self.write(").toUInt()");
                if little_endian {
                    for i in 0..4 {
                        let shift = i * 8;
                        if shift > 0 {
                            self.write(&format!(
                                "; __arr[__s + {}] = ((__v shr {}) and 0xFFu).toUByte()",
                                i, shift
                            ));
                        } else {
                            self.write(&format!(
                                "; __arr[__s + {}] = (__v and 0xFFu).toUByte()",
                                i
                            ));
                        }
                    }
                } else {
                    for i in 0..4 {
                        let shift = (3 - i) * 8;
                        if shift > 0 {
                            self.write(&format!(
                                "; __arr[__s + {}] = ((__v shr {}) and 0xFFu).toUByte()",
                                i, shift
                            ));
                        } else {
                            self.write(&format!(
                                "; __arr[__s + {}] = (__v and 0xFFu).toUByte()",
                                i
                            ));
                        }
                    }
                }
            }
            PrimitiveType::U64 | PrimitiveType::I64 => {
                self.write(").toULong()");
                if little_endian {
                    for i in 0..8 {
                        let shift = i * 8;
                        if shift > 0 {
                            self.write(&format!(
                                "; __arr[__s + {}] = ((__v shr {}) and 0xFFuL).toUByte()",
                                i, shift
                            ));
                        } else {
                            self.write(&format!(
                                "; __arr[__s + {}] = (__v and 0xFFuL).toUByte()",
                                i
                            ));
                        }
                    }
                } else {
                    for i in 0..8 {
                        let shift = (7 - i) * 8;
                        if shift > 0 {
                            self.write(&format!(
                                "; __arr[__s + {}] = ((__v shr {}) and 0xFFuL).toUByte()",
                                i, shift
                            ));
                        } else {
                            self.write(&format!(
                                "; __arr[__s + {}] = (__v and 0xFFuL).toUByte()",
                                i
                            ));
                        }
                    }
                }
            }
            _ => {
                self.write(").toUInt()");
                // fallback to u32
                if little_endian {
                    for i in 0..4 {
                        let shift = i * 8;
                        if shift > 0 {
                            self.write(&format!(
                                "; __arr[__s + {}] = ((__v shr {}) and 0xFFu).toUByte()",
                                i, shift
                            ));
                        } else {
                            self.write(&format!(
                                "; __arr[__s + {}] = (__v and 0xFFu).toUByte()",
                                i
                            ));
                        }
                    }
                } else {
                    for i in 0..4 {
                        let shift = (3 - i) * 8;
                        if shift > 0 {
                            self.write(&format!(
                                "; __arr[__s + {}] = ((__v shr {}) and 0xFFu).toUByte()",
                                i, shift
                            ));
                        } else {
                            self.write(&format!(
                                "; __arr[__s + {}] = (__v and 0xFFu).toUByte()",
                                i
                            ));
                        }
                    }
                }
            }
        }

        self.write(" }\n");
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

/// Check if an expression is a boolean (not numeric), used to avoid .toULong() on booleans
fn is_bool_like_expr(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Bool(_) => true,
        ExprKind::Binary { op, .. } => matches!(
            op,
            BinaryOp::Eq
                | BinaryOp::Ne
                | BinaryOp::Lt
                | BinaryOp::Le
                | BinaryOp::Gt
                | BinaryOp::Ge
                | BinaryOp::And
                | BinaryOp::Or
        ),
        ExprKind::Unary {
            op: UnaryOp::Not, ..
        } => true,
        ExprKind::Paren(inner) => is_bool_like_expr(inner),
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

impl Default for KotlinGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for KotlinGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();
        self.var_elem_types.clear();

        // Pre-pass: collect struct field info and methods
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
        self.writeln("@file:OptIn(ExperimentalUnsignedTypes::class)");
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
            self.writeln("fun runTests(): Boolean {");
            self.indent();
            self.writeln("var __passed = 0");
            self.writeln("var __failed = 0");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("__test_name = \"{}\"", name));
                self.writeln("__test_failures = 0");
                self.writeln("try {");
                self.indent();
                self.writeln(&format!("test_{}()", name));
                self.writeln("if (__test_failures == 0) {");
                self.indent();
                self.writeln(&format!("println(\"PASS: {}\")", name));
                self.writeln("__passed++");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("println(\"FAIL: {}\")", name));
                self.writeln("__failed++");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("} catch (e: Exception) {");
                self.indent();
                self.writeln(&format!("println(\"FAIL: {} - ${{e.message}}\")", name));
                self.writeln("__failed++");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("println()");
            self.writeln("println(\"$__passed passed, $__failed failed\")");
            self.writeln("return __failed == 0");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // Generate main function
        if self.include_tests {
            self.writeln("fun main() {");
            self.indent();
            self.writeln("val success = runTests()");
            self.writeln("if (!success) {");
            self.indent();
            self.writeln("kotlin.system.exitProcess(1)");
            self.dedent();
            self.writeln("}");
            self.dedent();
            self.writeln("}");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "kt"
    }

    fn language_name(&self) -> &'static str {
        "Kotlin"
    }
}

fn escape_kotlin_string(s: &str) -> String {
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
