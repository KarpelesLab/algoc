//! Java code generator
//!
//! Generates Java code from the analyzed AST.
//! Produces a single `AlgocTest` class with all functions as static methods.
//! Java has no unsigned types, so we use masking (& 0xFF, & 0xFFFF, etc.)
//! and Integer.toUnsignedXxx / Long.toUnsignedXxx for unsigned semantics.

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

/// Java code generator
pub struct JavaGenerator {
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
    /// Variables known to have byte (u8/i8) type
    byte_vars: HashSet<String>,
    /// Variables known to have byte[] (u8[]/i8[]) array type
    byte_array_vars: HashSet<String>,
}

impl JavaGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            byte_vars: HashSet::new(),
            byte_array_vars: HashSet::new(),
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

    // -----------------------------------------------------------------------
    // Type mapping helpers
    // -----------------------------------------------------------------------

    /// Map an AlgoC type to its Java representation.
    fn java_type(ty: &ParserType) -> String {
        use crate::parser::TypeKind;

        match &ty.kind {
            TypeKind::Primitive(p) => Self::java_primitive_type(&p.to_native()),
            TypeKind::Array { element, .. }
            | TypeKind::Slice { element }
            | TypeKind::ArrayRef { element, .. } => {
                format!("{}[]", Self::java_type(element))
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                match &inner.kind {
                    TypeKind::Primitive(p) => {
                        // Mutable references to primitives: wrap in single-element array
                        format!("{}[]", Self::java_primitive_type(&p.to_native()))
                    }
                    TypeKind::Array { element, .. }
                    | TypeKind::Slice { element }
                    | TypeKind::ArrayRef { element, .. } => {
                        format!("{}[]", Self::java_type(element))
                    }
                    _ => Self::java_type(inner),
                }
            }
            TypeKind::Named(ident) => ident.name.clone(),
            TypeKind::SelfType => "Object".to_string(),
        }
    }

    fn java_primitive_type(p: &crate::parser::PrimitiveType) -> String {
        use crate::parser::PrimitiveType;
        match p {
            PrimitiveType::U8 | PrimitiveType::I8 => "byte".to_string(),
            PrimitiveType::U16 | PrimitiveType::I16 => "short".to_string(),
            PrimitiveType::U32 | PrimitiveType::I32 => "int".to_string(),
            PrimitiveType::U64 | PrimitiveType::I64 => "long".to_string(),
            PrimitiveType::U128 | PrimitiveType::I128 => "long".to_string(), // best we can do natively
            PrimitiveType::Bool => "boolean".to_string(),
            // Endian variants map to same native type
            _ => Self::java_primitive_type(&p.to_native()),
        }
    }

    /// Default value for a Java type (used in struct constructors and uninitialised lets)
    fn default_value_for_type(&self, ty: &ParserType) -> String {
        use crate::parser::{PrimitiveType, TypeKind};

        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::Bool => "false".to_string(),
                    PrimitiveType::U64
                    | PrimitiveType::I64
                    | PrimitiveType::U128
                    | PrimitiveType::I128 => "0L".to_string(),
                    _ => "0".to_string(),
                }
            }
            TypeKind::Array { element, size } => {
                format!("new {}[{}]", Self::java_type(element), size)
            }
            TypeKind::Named(ident) => format!("new {}()", ident.name),
            _ => "null".to_string(),
        }
    }

    /// Whether a type maps to Java `byte`
    fn is_byte_primitive(ty: &ParserType) -> bool {
        use crate::parser::{PrimitiveType, TypeKind};
        if let TypeKind::Primitive(p) = &ty.kind {
            matches!(p.to_native(), PrimitiveType::U8 | PrimitiveType::I8)
        } else {
            false
        }
    }

    /// Whether a type maps to Java `byte[]` (array/slice/ref of u8/i8)
    fn is_byte_array_type(ty: &ParserType) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Array { element, .. }
            | TypeKind::Slice { element }
            | TypeKind::ArrayRef { element, .. } => Self::is_byte_primitive(element),
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => match &inner.kind {
                TypeKind::Array { element, .. }
                | TypeKind::Slice { element }
                | TypeKind::ArrayRef { element, .. } => Self::is_byte_primitive(element),
                _ => false,
            },
            _ => false,
        }
    }

    /// Whether a primitive type is 64-bit (long) in Java
    fn is_long_type(p: &crate::parser::PrimitiveType) -> bool {
        use crate::parser::PrimitiveType;
        let n = p.to_native();
        matches!(
            n,
            PrimitiveType::U64 | PrimitiveType::I64 | PrimitiveType::U128 | PrimitiveType::I128
        )
    }

    /// Check if an assignment target expression refers to a byte-typed location.
    /// Returns true if assigning to this target requires a `(byte)` cast on the value.
    fn target_is_byte(&self, target: &Expr) -> bool {
        match &target.kind {
            ExprKind::Ident(ident) => self.byte_vars.contains(&ident.name),
            ExprKind::Index { array, .. } => {
                // Check if the array is a known byte array variable
                if let ExprKind::Ident(ident) = &array.kind {
                    self.byte_array_vars.contains(&ident.name)
                } else if let ExprKind::Field { object, field } = &array.kind {
                    // struct_field: check if the struct field is a byte array
                    if let ExprKind::Ident(obj_ident) = &object.kind
                        && let Some(struct_name) = self.var_types.get(&obj_ident.name)
                        && let Some(fields) = self.struct_defs.get(struct_name)
                    {
                        for f in fields {
                            if f.name == field.name && Self::is_byte_array_type(&f.ty) {
                                return true;
                            }
                        }
                    }
                    false
                } else {
                    false
                }
            }
            ExprKind::Field { object, field } => {
                // Check struct field type
                if let ExprKind::Ident(obj_ident) = &object.kind
                    && let Some(struct_name) = self.var_types.get(&obj_ident.name)
                    && let Some(fields) = self.struct_defs.get(struct_name)
                {
                    for f in fields {
                        if f.name == field.name && Self::is_byte_primitive(&f.ty) {
                            return true;
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Register byte type tracking for function/method parameters
    fn register_param_byte_types(&mut self, params: &[crate::parser::Param]) {
        for param in params {
            if Self::is_byte_primitive(&param.ty) {
                self.byte_vars.insert(param.name.name.clone());
            } else if Self::is_byte_array_type(&param.ty) {
                self.byte_array_vars.insert(param.name.name.clone());
            }
        }
    }

    // -----------------------------------------------------------------------
    // Runtime / helpers
    // -----------------------------------------------------------------------

    /// Generate the runtime helper methods inside the class.
    fn generate_runtime(&mut self) {
        // Reader inner class
        self.writeln("static class Reader {");
        self.indent();
        self.writeln("private final byte[] data;");
        self.writeln("private int pos;");
        self.writeln("Reader(byte[] data) { this.data = data; this.pos = 0; }");
        self.writeln("int read_u8() { return data[pos++] & 0xFF; }");
        // read_u16be / read_u16le
        self.writeln("int read_u16() { return read_u16be(); }");
        self.writeln("int read_u16be() { int v = ((data[pos] & 0xFF) << 8) | (data[pos+1] & 0xFF); pos += 2; return v; }");
        self.writeln("int read_u16le() { int v = (data[pos] & 0xFF) | ((data[pos+1] & 0xFF) << 8); pos += 2; return v; }");
        // read_u32be / read_u32le
        self.writeln("int read_u32() { return read_u32be(); }");
        self.writeln("int read_u32be() { int v = ((data[pos] & 0xFF) << 24) | ((data[pos+1] & 0xFF) << 16) | ((data[pos+2] & 0xFF) << 8) | (data[pos+3] & 0xFF); pos += 4; return v; }");
        self.writeln("int read_u32le() { int v = (data[pos] & 0xFF) | ((data[pos+1] & 0xFF) << 8) | ((data[pos+2] & 0xFF) << 16) | ((data[pos+3] & 0xFF) << 24); pos += 4; return v; }");
        // read_u64be / read_u64le
        self.writeln("long read_u64() { return read_u64be(); }");
        self.writeln("long read_u64be() { long v = 0; for (int i = 0; i < 8; i++) v = (v << 8) | (data[pos+i] & 0xFF); pos += 8; return v; }");
        self.writeln("long read_u64le() { long v = 0; for (int i = 7; i >= 0; i--) v = (v << 8) | (data[pos+i] & 0xFF); pos += 8; return v; }");
        // read_bytes
        self.writeln("byte[] read_bytes(int count) { byte[] r = java.util.Arrays.copyOfRange(data, pos, pos + count); pos += count; return r; }");
        // read_chunk
        self.writeln("byte[] read_chunk(int max_size) { int count = Math.min(max_size, data.length - pos); byte[] r = java.util.Arrays.copyOfRange(data, pos, pos + count); pos += count; return r; }");
        // eof
        self.writeln("boolean eof() { return pos >= data.length; }");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer inner class
        self.writeln("static class Writer {");
        self.indent();
        self.writeln("private final byte[] data;");
        self.writeln("private int pos;");
        self.writeln("Writer(byte[] data) { this.data = data; this.pos = 0; }");
        self.writeln("void write_u8(int v) { data[pos++] = (byte)(v & 0xFF); }");
        // write_u16
        self.writeln("void write_u16(int v) { write_u16be(v); }");
        self.writeln("void write_u16be(int v) { data[pos] = (byte)((v >> 8) & 0xFF); data[pos+1] = (byte)(v & 0xFF); pos += 2; }");
        self.writeln("void write_u16le(int v) { data[pos] = (byte)(v & 0xFF); data[pos+1] = (byte)((v >> 8) & 0xFF); pos += 2; }");
        // write_u32
        self.writeln("void write_u32(int v) { write_u32be(v); }");
        self.writeln("void write_u32be(int v) { data[pos] = (byte)((v >> 24) & 0xFF); data[pos+1] = (byte)((v >> 16) & 0xFF); data[pos+2] = (byte)((v >> 8) & 0xFF); data[pos+3] = (byte)(v & 0xFF); pos += 4; }");
        self.writeln("void write_u32le(int v) { data[pos] = (byte)(v & 0xFF); data[pos+1] = (byte)((v >> 8) & 0xFF); data[pos+2] = (byte)((v >> 16) & 0xFF); data[pos+3] = (byte)((v >> 24) & 0xFF); pos += 4; }");
        // write_u64
        self.writeln("void write_u64(long v) { write_u64be(v); }");
        self.writeln("void write_u64be(long v) { for (int i = 7; i >= 0; i--) { data[pos + 7 - i] = (byte)((v >> (i * 8)) & 0xFF); } pos += 8; }");
        self.writeln("void write_u64le(long v) { for (int i = 0; i < 8; i++) { data[pos + i] = (byte)((v >> (i * 8)) & 0xFF); } pos += 8; }");
        // write_bytes
        self.writeln("void write_bytes(byte[] src) { System.arraycopy(src, 0, data, pos, src.length); pos += src.length; }");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Generate test runtime helpers
    fn generate_test_runtime(&mut self) {
        self.writeln("static int __test_failures = 0;");
        self.writeln("static String __test_name = \"\";");
        self.writeln("");

        self.writeln("static void __assert(boolean condition) {");
        self.indent();
        self.writeln("if (!condition) {");
        self.indent();
        self.writeln("__test_failures++;");
        self.writeln("System.out.println(\"  ASSERTION FAILED in \" + __test_name);");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    // -----------------------------------------------------------------------
    // AST traversal
    // -----------------------------------------------------------------------

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
                // Use statements are handled during loading, items already merged
            }
            ItemKind::Impl(impl_def) => {
                for method in &impl_def.methods {
                    self.generate_method(&impl_def.target.name, method);
                }
            }
            ItemKind::Interface(_) => {
                // Interfaces are compile-time only
            }
        }
    }

    // -----------------------------------------------------------------------
    // Top-level items
    // -----------------------------------------------------------------------

    fn generate_function(&mut self, func: &Function) {
        self.write_indent();
        // Return type
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!("static {} ", Self::java_type(ret_ty)));
        } else {
            self.write("static void ");
        }
        self.write(&format!("{}(", func.name.name));

        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&format!(
                "{} {}",
                Self::java_type(&param.ty),
                param.name.name
            ));
        }

        self.write(") {\n");
        self.indent();
        // Save and reset byte tracking for this function scope
        let saved_byte_vars = std::mem::take(&mut self.byte_vars);
        let saved_byte_array_vars = std::mem::take(&mut self.byte_array_vars);
        self.register_param_byte_types(&func.params);
        self.generate_block(&func.body);
        self.byte_vars = saved_byte_vars;
        self.byte_array_vars = saved_byte_array_vars;
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_method(&mut self, struct_name: &str, func: &Function) {
        let mangled_name = format!("{}__{}", struct_name, func.name.name);
        self.write_indent();
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!("static {} ", Self::java_type(ret_ty)));
        } else {
            self.write("static void ");
        }
        self.write(&format!("{}(", mangled_name));

        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&format!(
                "{} {}",
                Self::java_type(&param.ty),
                param.name.name
            ));
        }

        self.write(") {\n");
        self.indent();
        let saved_byte_vars = std::mem::take(&mut self.byte_vars);
        let saved_byte_array_vars = std::mem::take(&mut self.byte_array_vars);
        self.register_param_byte_types(&func.params);
        self.generate_block(&func.body);
        self.byte_vars = saved_byte_vars;
        self.byte_array_vars = saved_byte_array_vars;
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("static void test_{}() {{", test.name.name));
        self.indent();
        let saved_byte_vars = std::mem::take(&mut self.byte_vars);
        let saved_byte_array_vars = std::mem::take(&mut self.byte_array_vars);
        self.generate_block(&test.body);
        self.byte_vars = saved_byte_vars;
        self.byte_array_vars = saved_byte_array_vars;
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        self.write(&format!(
            "static final {} {} = ",
            Self::java_type(&c.ty),
            c.name.name
        ));
        self.generate_expr(&c.value);
        self.write(";\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        self.writeln(&format!("static class {} {{", s.name.name));
        self.indent();
        for field in &s.fields {
            let jt = Self::java_type(&field.ty);
            let def = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{} {} = {};", jt, field.name.name, def));
        }
        // clone method for struct copying
        self.writeln(&format!("{} copy() {{", s.name.name));
        self.indent();
        self.writeln(&format!("{} c = new {}();", s.name.name, s.name.name));
        for field in &s.fields {
            match &field.ty.kind {
                crate::parser::TypeKind::Array { .. } => {
                    self.writeln(&format!("c.{f} = {f}.clone();", f = field.name.name));
                }
                _ => {
                    self.writeln(&format!("c.{f} = this.{f};", f = field.name.name));
                }
            }
        }
        self.writeln("return c;");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Generate same as struct (layouts are struct-like)
        self.writeln(&format!("static class {} {{", l.name.name));
        self.indent();
        for field in &l.fields {
            let jt = Self::java_type(&field.ty);
            let def = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{} {} = {};", jt, field.name.name, def));
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate as a static inner class with a tag field and variant data fields
        self.writeln(&format!("static class {} {{", e.name.name));
        self.indent();
        self.writeln("String tag;");

        // Collect all possible data fields across variants
        let mut seen_tuple_fields = 0usize;
        let mut seen_struct_fields: Vec<String> = Vec::new();
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {}
                crate::parser::EnumVariantData::Tuple(types) => {
                    if types.len() > seen_tuple_fields {
                        seen_tuple_fields = types.len();
                    }
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    for f in fields {
                        if !seen_struct_fields.contains(&f.name.name) {
                            seen_struct_fields.push(f.name.name.clone());
                        }
                    }
                }
            }
        }
        // Use Object for variant data fields since types may differ
        for i in 0..seen_tuple_fields {
            self.writeln(&format!("Object v{};", i));
        }
        for name in &seen_struct_fields {
            self.writeln(&format!("Object {};", name));
        }

        // Constructor helpers as static methods
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!(
                        "static {} {}() {{",
                        e.name.name, variant.name.name
                    ));
                    self.indent();
                    self.writeln(&format!("{} o = new {}();", e.name.name, e.name.name));
                    self.writeln(&format!("o.tag = \"{}\";", variant.name.name));
                    self.writeln("return o;");
                    self.dedent();
                    self.writeln("}");
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    let params: Vec<String> = types
                        .iter()
                        .enumerate()
                        .map(|(i, _)| format!("Object p{}", i))
                        .collect();
                    self.writeln(&format!(
                        "static {} {}({}) {{",
                        e.name.name,
                        variant.name.name,
                        params.join(", ")
                    ));
                    self.indent();
                    self.writeln(&format!("{} o = new {}();", e.name.name, e.name.name));
                    self.writeln(&format!("o.tag = \"{}\";", variant.name.name));
                    for i in 0..types.len() {
                        self.writeln(&format!("o.v{} = p{};", i, i));
                    }
                    self.writeln("return o;");
                    self.dedent();
                    self.writeln("}");
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    let params: Vec<String> = fields
                        .iter()
                        .map(|f| format!("Object {}", f.name.name))
                        .collect();
                    self.writeln(&format!(
                        "static {} {}({}) {{",
                        e.name.name,
                        variant.name.name,
                        params.join(", ")
                    ));
                    self.indent();
                    self.writeln(&format!("{} o = new {}();", e.name.name, e.name.name));
                    self.writeln(&format!("o.tag = \"{}\";", variant.name.name));
                    for f in fields {
                        self.writeln(&format!("o.{} = {};", f.name.name, f.name.name));
                    }
                    self.writeln("return o;");
                    self.dedent();
                    self.writeln("}");
                }
            }
        }

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    // -----------------------------------------------------------------------
    // Blocks / Statements
    // -----------------------------------------------------------------------

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
                // Track byte and byte-array variables
                if let Some(ty) = ty {
                    if Self::is_byte_primitive(ty) {
                        self.byte_vars.insert(name.name.clone());
                    } else if Self::is_byte_array_type(ty) {
                        self.byte_array_vars.insert(name.name.clone());
                    }
                }
                // Infer type from static method calls like TypeName__new()
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
                // Determine Java type
                let needs_byte_cast = ty.as_ref().is_some_and(Self::is_byte_primitive);
                if let Some(ty) = ty {
                    self.write(&format!("{} {} = ", Self::java_type(ty), name.name));
                    if let Some(init) = init {
                        if needs_byte_cast && Self::expr_may_widen_to_int(init) {
                            self.write("(byte)(");
                            self.generate_expr(init);
                            self.write(")");
                        } else {
                            self.generate_expr(init);
                        }
                    } else {
                        self.write(&self.default_value_for_type(ty));
                    }
                } else if let Some(init) = init {
                    // No explicit type - infer from init expression
                    let inferred_type = Self::infer_java_type(init);
                    self.write(&format!("{} {} = ", inferred_type, name.name));
                    self.generate_expr(init);
                } else {
                    // Neither type nor init - shouldn't happen, but use Object
                    self.write(&format!("Object {} = null", name.name));
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
                        self.write_indent();
                        self.write("{ byte[] __target = ");
                        self.generate_expr(array);
                        self.write("; int __off = (int)(");
                        self.generate_expr(start);
                        self.write("); ");
                        let little_endian = endian == crate::parser::Endianness::Little;
                        let native = p.to_native();
                        match native {
                            crate::parser::PrimitiveType::U16
                            | crate::parser::PrimitiveType::I16 => {
                                self.write("int __v = (int)(");
                                self.generate_expr(value);
                                self.write("); ");
                                if little_endian {
                                    self.write("__target[__off] = (byte)(__v & 0xFF); __target[__off+1] = (byte)((__v >> 8) & 0xFF);");
                                } else {
                                    self.write("__target[__off] = (byte)((__v >> 8) & 0xFF); __target[__off+1] = (byte)(__v & 0xFF);");
                                }
                            }
                            crate::parser::PrimitiveType::U32
                            | crate::parser::PrimitiveType::I32 => {
                                self.write("int __v = (int)(");
                                self.generate_expr(value);
                                self.write("); ");
                                if little_endian {
                                    self.write("__target[__off] = (byte)(__v & 0xFF); __target[__off+1] = (byte)((__v >> 8) & 0xFF); __target[__off+2] = (byte)((__v >> 16) & 0xFF); __target[__off+3] = (byte)((__v >> 24) & 0xFF);");
                                } else {
                                    self.write("__target[__off] = (byte)((__v >> 24) & 0xFF); __target[__off+1] = (byte)((__v >> 16) & 0xFF); __target[__off+2] = (byte)((__v >> 8) & 0xFF); __target[__off+3] = (byte)(__v & 0xFF);");
                                }
                            }
                            crate::parser::PrimitiveType::U64
                            | crate::parser::PrimitiveType::I64 => {
                                self.write("long __v = (long)(");
                                self.generate_expr(value);
                                self.write("); ");
                                if little_endian {
                                    self.write("for (int __i = 0; __i < 8; __i++) { __target[__off + __i] = (byte)((__v >> (__i * 8)) & 0xFF); }");
                                } else {
                                    self.write("for (int __i = 0; __i < 8; __i++) { __target[__off + 7 - __i] = (byte)((__v >> (__i * 8)) & 0xFF); }");
                                }
                            }
                            _ => {
                                // fallback - 32-bit
                                self.write("int __v = (int)(");
                                self.generate_expr(value);
                                self.write("); ");
                                if little_endian {
                                    self.write("__target[__off] = (byte)(__v & 0xFF); __target[__off+1] = (byte)((__v >> 8) & 0xFF); __target[__off+2] = (byte)((__v >> 16) & 0xFF); __target[__off+3] = (byte)((__v >> 24) & 0xFF);");
                                } else {
                                    self.write("__target[__off] = (byte)((__v >> 24) & 0xFF); __target[__off+1] = (byte)((__v >> 16) & 0xFF); __target[__off+2] = (byte)((__v >> 8) & 0xFF); __target[__off+3] = (byte)(__v & 0xFF);");
                                }
                            }
                        }
                        self.write(" }\n");
                        return;
                    }
                }

                let needs_byte_cast = self.target_is_byte(target);
                self.write_indent();
                self.generate_expr(target);
                self.write(" = ");
                if needs_byte_cast {
                    self.write("(byte)(");
                    self.generate_expr(value);
                    self.write(")");
                } else {
                    self.generate_expr(value);
                }
                self.write(";\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                let needs_byte_cast = self.target_is_byte(target);
                if needs_byte_cast {
                    // Expand compound assignment to avoid lossy int->byte narrowing.
                    // E.g. `result |= x` becomes `result = (byte)(result | x)`
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
                        BinaryOp::Shr => " >>> ",
                        _ => " | ",
                    };
                    self.write_indent();
                    self.generate_expr(target);
                    self.write(" = (byte)(");
                    self.generate_expr(target);
                    self.write(op_str);
                    self.generate_expr(value);
                    self.write(");\n");
                } else {
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
                // Detect if we need long loop variable
                let use_long = Self::expr_needs_long(start) || Self::expr_needs_long(end);
                let type_str = if use_long { "long" } else { "int" };
                let cmp = if *inclusive { "<=" } else { "<" };
                self.write_indent();
                self.write(&format!("for ({} {} = ", type_str, var.name));
                self.generate_expr(start);
                self.write(&format!("; {} {} ", var.name, cmp));
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
                if let Some(expr) = expr {
                    self.write("return ");
                    self.generate_expr(expr);
                    self.write(";\n");
                } else {
                    self.write("return;\n");
                }
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

    // -----------------------------------------------------------------------
    // Expressions
    // -----------------------------------------------------------------------

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                // Integers that fit in int use plain literals,
                // those that need long get an L suffix.
                if *n > i32::MAX as u128 {
                    self.write(&format!("{}L", n));
                } else {
                    self.write(&format!("{}", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // String to byte array
                self.write(&format!(
                    "\"{}\".getBytes(java.nio.charset.StandardCharsets.UTF_8)",
                    escape_java_string(s)
                ));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!(
                    "\"{}\".getBytes(java.nio.charset.StandardCharsets.UTF_8)",
                    escape_java_string(s)
                ));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to byte array literal
                let bytes: Vec<String> = hex_string_to_bytes(h)
                    .iter()
                    .map(|b| format!("(byte)0x{:02X}", b))
                    .collect();
                self.write(&format!("new byte[]{{{}}}", bytes.join(", ")));
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                // For array/byte-array comparisons, use constant_time_eq
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
                    BinaryOp::Shr => " >>> ", // unsigned right shift in Java
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
                self.write("(int)(");
                self.generate_expr(index);
                self.write(")");
                self.write("]");
            }
            ExprKind::Slice {
                array,
                start,
                end,
                inclusive,
            } => {
                self.write("java.util.Arrays.copyOfRange(");
                self.generate_expr(array);
                self.write(", (int)(");
                self.generate_expr(start);
                self.write("), (int)(");
                self.generate_expr(end);
                if *inclusive {
                    self.write(") + 1)");
                } else {
                    self.write("))");
                }
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
                        self.generate_expr(object);
                        self.write(".length");
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
                            // Reader read_bytes / read_chunk take int
                            if (field.name == "read_bytes" || field.name == "read_chunk") && i == 0
                            {
                                self.write("(int)(");
                                self.generate_expr(arg);
                                self.write(")");
                            } else {
                                self.generate_expr(arg);
                            }
                        }
                        self.write(")");
                        return;
                    }

                    // Struct method calls (object.method(args))
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

                // Normal function call
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
                    self.write("new byte[0]");
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
                        self.write("new byte[]{");
                        for (i, elem) in elements.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.write("(byte)");
                            self.generate_expr(elem);
                        }
                        self.write("}");
                    } else {
                        // Use int array as default
                        self.write("new int[]{");
                        for (i, elem) in elements.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_expr(elem);
                        }
                        self.write("}");
                    }
                }
            }
            ExprKind::ArrayRepeat { value, count } => {
                // Need to determine element type
                let is_byte = is_byte_value(value);
                if is_byte {
                    self.write("new byte[(int)(");
                    self.generate_expr(count);
                    self.write(")]");
                    // Java initialises to 0, so only fill if non-zero
                    if !matches!(value.kind, ExprKind::Integer(0)) {
                        self.write(" /* fill: ");
                        self.generate_expr(value);
                        self.write(" */");
                        // We can't chain in Java easily. We'll use a helper pattern.
                        // Instead, generate an IIFE-like static block ... but Java can't do that inline.
                        // Rewrite as: __fillByte(new byte[N], val)
                        // Actually, let's just do it properly with a lambda won't work.
                        // Best approach: generate the fill call using Arrays.fill in a block.
                        // Since this is used as an expression, we need a helper approach.
                        // Let's output it differently.
                    }
                } else {
                    self.write("new int[(int)(");
                    self.generate_expr(count);
                    self.write(")]");
                }
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // In Java, arrays/objects already pass by reference.
                // For primitive mutable references, the caller should have declared int[] etc.
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are no-ops for objects/arrays in Java
                self.generate_expr(inner);
            }
            ExprKind::Range { .. } => {
                // Ranges are handled by for loops - should not appear standalone
                self.write("/* range */");
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.generate_expr(inner);
                self.write(")");
            }
            ExprKind::StructLit { name, fields } => {
                // Create a new struct instance and set fields
                // In Java we need a block expression - use a helper lambda pattern
                // Since Java doesn't have expression blocks, we use an immediately invoked pattern:
                // ((Supplier<StructName>)(() -> { StructName o = new StructName(); o.f1 = v1; ... return o; })).get()
                // Simpler: just use a static helper. But for inline, let's do:
                self.write(&format!("new {}() {{ {{ ", name.name));
                for (field_name, value) in fields {
                    self.write(&format!("{} = ", field_name.name));
                    self.generate_expr(value);
                    self.write("; ");
                }
                self.write("} }");
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
                self.write(&format!("{}.{}(", enum_name.name, variant_name.name));
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_expr(arg);
                }
                self.write(")");
            }
            ExprKind::Match { expr, arms } => {
                // Java doesn't have match expressions easily.
                // Generate as a chain of ternaries or use a lambda IIFE pattern.
                // Use: ((java.util.function.Function<EnumType, RetType>) (__match -> { ... })).apply(expr)
                // Simpler: use a helper approach with a block.
                // Actually, the simplest approach is a chained ternary for simple cases,
                // or an IIFE lambda.
                self.write("((java.util.function.Supplier<Object>)(() -> { ");
                self.write("var __match = ");
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
                self.write(" return null; })).get()");
            }
            ExprKind::MethodCall {
                receiver,
                mangled_name,
                args,
                ..
            } => {
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
                // Should be resolved by monomorphization
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

    // -----------------------------------------------------------------------
    // Pattern matching
    // -----------------------------------------------------------------------

    fn generate_pattern_match(&mut self, pattern: &crate::parser::Pattern, scrutinee: &str) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("if (true)");
            }
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("if ({} == (Object)(", scrutinee));
                self.generate_expr(lit_expr);
                self.write("))");
            }
            PatternKind::Ident(ident) => {
                self.write(&format!(
                    "if (((java.util.function.Supplier<Boolean>)(() -> {{ var {} = {}; return true; }})).get())",
                    ident.name, scrutinee
                ));
            }
            PatternKind::EnumVariant {
                variant_name,
                bindings,
                ..
            } => {
                self.write(&format!(
                    "if ({}.tag.equals(\"{}\")",
                    scrutinee, variant_name.name
                ));
                if !bindings.is_empty() {
                    // Bindings extraction would go here
                }
                self.write(")");
            }
            PatternKind::Tuple(_patterns) => {
                self.write("if (true)");
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
                self.write(&format!("{} == (Object)(", scrutinee));
                self.generate_expr(lit_expr);
                self.write(")");
            }
            PatternKind::Ident(_) => self.write("true"),
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!(
                    "{}.tag.equals(\"{}\")",
                    scrutinee, variant_name.name
                ));
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

    // -----------------------------------------------------------------------
    // Casts
    // -----------------------------------------------------------------------

    fn generate_cast(&mut self, expr: &Expr, ty: &ParserType) {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        // Endian byte conversions (byte slice to integer)
        if let TypeKind::Primitive(p) = &ty.kind {
            let endian = p.endianness();
            if endian != Endianness::Native {
                let little_endian = endian == Endianness::Little;
                let native = p.to_native();

                // Source is a byte sequence -> read bytes as integer
                if is_byte_sequence_expr(expr) {
                    match native {
                        PrimitiveType::U16 | PrimitiveType::I16 => {
                            self.write("((int)(() -> { byte[] __b = ");
                            // Can't do lambdas inline cleanly, use block helper
                            // Instead, generate inline byte reading
                            self.write("/* u16 from bytes */ ((java.util.function.Supplier<Integer>)(() -> { byte[] __b = ");
                            self.generate_expr(expr);
                            if little_endian {
                                self.write(
                                    "; return (__b[0] & 0xFF) | ((__b[1] & 0xFF) << 8); })).get()",
                                );
                            } else {
                                self.write(
                                    "; return ((__b[0] & 0xFF) << 8) | (__b[1] & 0xFF); })).get()",
                                );
                            }
                            return;
                        }
                        PrimitiveType::U32 | PrimitiveType::I32 => {
                            self.write(
                                "((java.util.function.Supplier<Integer>)(() -> { byte[] __b = ",
                            );
                            self.generate_expr(expr);
                            if little_endian {
                                self.write("; return (__b[0] & 0xFF) | ((__b[1] & 0xFF) << 8) | ((__b[2] & 0xFF) << 16) | ((__b[3] & 0xFF) << 24); })).get()");
                            } else {
                                self.write("; return ((__b[0] & 0xFF) << 24) | ((__b[1] & 0xFF) << 16) | ((__b[2] & 0xFF) << 8) | (__b[3] & 0xFF); })).get()");
                            }
                            return;
                        }
                        PrimitiveType::U64 | PrimitiveType::I64 => {
                            self.write(
                                "((java.util.function.Supplier<Long>)(() -> { byte[] __b = ",
                            );
                            self.generate_expr(expr);
                            self.write("; long __v = 0L; ");
                            if little_endian {
                                self.write("for (int __i = 7; __i >= 0; __i--) __v = (__v << 8) | (__b[__i] & 0xFF);");
                            } else {
                                self.write("for (int __i = 0; __i < 8; __i++) __v = (__v << 8) | (__b[__i] & 0xFF);");
                            }
                            self.write(" return __v; })).get()");
                            return;
                        }
                        PrimitiveType::U128 | PrimitiveType::I128 => {
                            // Use two longs (high and low) - but we're mapping to single long
                            // This loses precision for values > 64 bits, but that's the best we can do
                            self.write(
                                "((java.util.function.Supplier<Long>)(() -> { byte[] __b = ",
                            );
                            self.generate_expr(expr);
                            self.write("; long __v = 0L; ");
                            if little_endian {
                                // Read only lower 8 bytes for long representation
                                self.write("for (int __i = 7; __i >= 0; __i--) __v = (__v << 8) | (__b[__i] & 0xFF);");
                            } else {
                                // Read upper 8 bytes (indices 8..15 for 128-bit)
                                self.write("for (int __i = 8; __i < 16; __i++) __v = (__v << 8) | (__b[__i] & 0xFF);");
                            }
                            self.write(" return __v; })).get()");
                            return;
                        }
                        _ => {} // fall through to standard cast
                    }
                }

                // Integer to integer with endian annotation - just treat as masking
                match native {
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        self.write("((short)(");
                        self.generate_expr(expr);
                        self.write(" & 0xFFFF))");
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        self.write("((int)(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        self.write("((long)(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    _ => {
                        self.write("((int)(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                }
                return;
            }
        }

        // Integer to byte array cast: value as u8[N]
        if let TypeKind::Array { element, size } = &ty.kind
            && let TypeKind::Primitive(PrimitiveType::U8) = &element.kind
        {
            let (little_endian, bits) = self.get_expr_endianness_info(expr);
            let inner_expr = if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                inner
            } else {
                expr
            };

            self.write(&format!(
                "((java.util.function.Supplier<byte[]>)(() -> {{ byte[] __a = new byte[{}]; ",
                size
            ));
            if bits <= 32 {
                self.write("int __v = (int)(");
                self.generate_expr(inner_expr);
                self.write("); ");
                if little_endian {
                    for i in 0..*size as usize {
                        self.write(&format!("__a[{}] = (byte)((__v >> {}) & 0xFF); ", i, i * 8));
                    }
                } else {
                    for i in 0..*size as usize {
                        self.write(&format!(
                            "__a[{}] = (byte)((__v >> {}) & 0xFF); ",
                            i,
                            (*size as usize - 1 - i) * 8
                        ));
                    }
                }
            } else {
                self.write("long __v = (long)(");
                self.generate_expr(inner_expr);
                self.write("); ");
                if little_endian {
                    for i in 0..*size as usize {
                        self.write(&format!("__a[{}] = (byte)((__v >> {}) & 0xFF); ", i, i * 8));
                    }
                } else {
                    for i in 0..*size as usize {
                        self.write(&format!(
                            "__a[{}] = (byte)((__v >> {}) & 0xFF); ",
                            i,
                            (*size as usize - 1 - i) * 8
                        ));
                    }
                }
            }
            self.write("return __a; })).get()");
            return;
        }

        // Standard casts
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => {
                        self.write("((byte)(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        self.write("((short)(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        self.write("((int)(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    PrimitiveType::U64
                    | PrimitiveType::I64
                    | PrimitiveType::U128
                    | PrimitiveType::I128 => {
                        self.write("((long)(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    PrimitiveType::Bool => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") != 0)");
                    }
                    _ => {
                        self.generate_expr(expr);
                    }
                }
            }
            _ => {
                // Non-primitive casts - just pass through
                self.write("(");
                self.generate_expr(expr);
                self.write(")");
            }
        }
    }

    // -----------------------------------------------------------------------
    // Builtins
    // -----------------------------------------------------------------------

    fn generate_builtin(&mut self, name: BuiltinFunc, args: &[Expr]) {
        match name {
            BuiltinFunc::Assert => {
                self.write("__assert(");
                self.generate_expr(&args[0]);
                self.write(")");
            }
        }
    }

    // -----------------------------------------------------------------------
    // Reader/Writer helpers
    // -----------------------------------------------------------------------

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

    // -----------------------------------------------------------------------
    // Type inference helpers
    // -----------------------------------------------------------------------

    /// Check if an expression could produce an `int` result when assigned to a `byte`.
    /// This is true for binary ops, unary ops, and other expressions that Java widens.
    /// Simple literals and explicit byte casts don't need wrapping.
    fn expr_may_widen_to_int(expr: &Expr) -> bool {
        match &expr.kind {
            // Binary operations always produce at least int in Java
            ExprKind::Binary { .. } => true,
            // Unary bitwise not produces int in Java
            ExprKind::Unary {
                op: UnaryOp::BitNot,
                ..
            } => true,
            ExprKind::Unary {
                op: UnaryOp::Neg, ..
            } => true,
            // An explicit cast to byte is already fine
            ExprKind::Cast { ty, .. } => {
                if let crate::parser::TypeKind::Primitive(p) = &ty.kind {
                    !matches!(
                        p.to_native(),
                        crate::parser::PrimitiveType::U8 | crate::parser::PrimitiveType::I8
                    )
                } else {
                    true
                }
            }
            // Array index on a byte array returns byte, no cast needed
            ExprKind::Index { .. } => false,
            // Integer literals that fit in byte don't strictly need it,
            // but values > 127 do since byte is signed in Java
            ExprKind::Integer(n) => *n > 127,
            // Function calls - we don't know the return type, be conservative
            ExprKind::Call { .. } => true,
            // Parenthesized - check inner
            ExprKind::Paren(inner) => Self::expr_may_widen_to_int(inner),
            // Conditionals - check branches
            ExprKind::Conditional {
                then_expr,
                else_expr,
                ..
            } => Self::expr_may_widen_to_int(then_expr) || Self::expr_may_widen_to_int(else_expr),
            // Variable references, field accesses - trust their declared type
            ExprKind::Ident(_) | ExprKind::Field { .. } => false,
            // Builtins, other - be conservative
            _ => false,
        }
    }

    /// Infer the Java type string for an expression that has no explicit type annotation.
    fn infer_java_type(expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Integer(n) => {
                if *n > i32::MAX as u128 {
                    "long".to_string()
                } else {
                    "int".to_string()
                }
            }
            ExprKind::Bool(_) => "boolean".to_string(),
            ExprKind::String(_) | ExprKind::Bytes(_) | ExprKind::Hex(_) => "byte[]".to_string(),
            ExprKind::Array(elems) => {
                if elems.is_empty() {
                    "byte[]".to_string()
                } else {
                    let all_bytes = elems.iter().all(|e| {
                        if let ExprKind::Integer(n) = &e.kind {
                            *n <= 255
                        } else {
                            false
                        }
                    });
                    if all_bytes {
                        "byte[]".to_string()
                    } else {
                        "int[]".to_string()
                    }
                }
            }
            ExprKind::ArrayRepeat { value, .. } => {
                if is_byte_value(value) {
                    "byte[]".to_string()
                } else {
                    "int[]".to_string()
                }
            }
            ExprKind::Cast { ty, .. } => Self::java_type(ty),
            ExprKind::StructLit { name, .. } => name.name.clone(),
            ExprKind::Call { func, .. } => {
                if let ExprKind::Ident(ident) = &func.kind {
                    if ident.name == "Reader" {
                        return "Reader".to_string();
                    }
                    if ident.name == "Writer" {
                        return "Writer".to_string();
                    }
                    if ident.name.contains("__new")
                        && let Some(idx) = ident.name.find("__new")
                    {
                        return ident.name[..idx].to_string();
                    }
                }
                "var".to_string()
            }
            ExprKind::Paren(inner) => Self::infer_java_type(inner),
            ExprKind::Slice { .. } => "byte[]".to_string(),
            ExprKind::EnumVariant { enum_name, .. } => enum_name.name.clone(),
            _ => "var".to_string(), // Java 10+ local variable type inference
        }
    }

    /// Check if an expression likely needs `long` type
    fn expr_needs_long(expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Integer(n) => *n > i32::MAX as u128,
            ExprKind::Cast { ty, .. } => {
                if let crate::parser::TypeKind::Primitive(p) = &ty.kind {
                    Self::is_long_type(p)
                } else {
                    false
                }
            }
            ExprKind::Paren(inner) => Self::expr_needs_long(inner),
            ExprKind::Binary { left, right, .. } => {
                Self::expr_needs_long(left) || Self::expr_needs_long(right)
            }
            _ => false,
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
        (true, 32)
    }
}

impl Default for JavaGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for JavaGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();
        self.byte_vars.clear();
        self.byte_array_vars.clear();

        // Pre-pass: collect struct definitions and methods
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

        // File header
        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("");
        self.writeln("import java.util.Arrays;");
        self.writeln("import java.nio.charset.StandardCharsets;");
        self.writeln("");

        // Start the class
        self.writeln("public class AlgocTest {");
        self.indent();
        self.writeln("");

        // Runtime helpers
        self.generate_runtime();

        if self.include_tests {
            self.generate_test_runtime();
        }

        // All items
        self.generate_ast(&ast.ast);

        // Test runner
        if self.include_tests {
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

            self.writeln("public static void main(String[] args) {");
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
                self.writeln(&format!("System.out.println(\"PASS: {}\");", name));
                self.writeln("__passed++;");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("System.out.println(\"FAIL: {}\");", name));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("} catch (Exception e) {");
                self.indent();
                self.writeln(&format!(
                    "System.out.println(\"FAIL: {} - \" + e.getMessage());",
                    name
                ));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("System.out.println(\"\");");
            self.writeln("System.out.println(__passed + \" passed, \" + __failed + \" failed\");");
            self.writeln("System.exit(__failed == 0 ? 0 : 1);");
            self.dedent();
            self.writeln("}");
        }

        // Close the class
        self.dedent();
        self.writeln("}");

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "java"
    }

    fn language_name(&self) -> &'static str {
        "Java"
    }
}

// ---------------------------------------------------------------------------
// Free helper functions
// ---------------------------------------------------------------------------

fn escape_java_string(s: &str) -> String {
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

fn hex_string_to_bytes(h: &str) -> Vec<u8> {
    let mut bytes = Vec::new();
    let chars: Vec<char> = h.chars().collect();
    let mut i = 0;
    while i + 1 < chars.len() {
        if let Ok(b) = u8::from_str_radix(&format!("{}{}", chars[i], chars[i + 1]), 16) {
            bytes.push(b);
        }
        i += 2;
    }
    bytes
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
