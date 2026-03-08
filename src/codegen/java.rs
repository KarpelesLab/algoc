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
    /// Current function's return type (for byte cast on return statements)
    current_return_type: Option<ParserType>,
    /// Variables declared in the current function scope (for avoiding
    /// duplicate `int i` declarations in for loops that shadow parameters)
    declared_vars: HashSet<String>,
    /// Function parameter types: func_name -> Vec<ParserType>
    func_param_types: HashMap<String, Vec<ParserType>>,
    /// Counter for generating unique loop variable names
    loop_var_counter: usize,
    /// Map from original loop variable names to renamed versions
    loop_var_renames: HashMap<String, String>,
    /// Current struct name for resolving SelfType (set during method/function generation)
    current_struct_name: Option<String>,
    /// Variables known to be non-u8 arrays (e.g., int[], long[])
    #[allow(dead_code)]
    non_u8_array_vars: HashSet<String>,
    /// Depth counter for nested struct literals (used to generate unique temp var names)
    struct_lit_depth: usize,
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
            current_return_type: None,
            declared_vars: HashSet::new(),
            func_param_types: HashMap::new(),
            loop_var_counter: 0,
            loop_var_renames: HashMap::new(),
            current_struct_name: None,
            non_u8_array_vars: HashSet::new(),
            struct_lit_depth: 0,
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
    fn java_type(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;

        match &ty.kind {
            TypeKind::Primitive(p) => Self::java_primitive_type(&p.to_native()),
            TypeKind::Array { element, .. }
            | TypeKind::Slice { element }
            | TypeKind::ArrayRef { element, .. } => {
                format!("{}[]", self.java_type(element))
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
                        format!("{}[]", self.java_type(element))
                    }
                    _ => self.java_type(inner),
                }
            }
            TypeKind::Named(ident) => {
                if ident.name == "Self" {
                    // Named("Self") should resolve like SelfType
                    if let Some(ref name) = self.current_struct_name {
                        name.clone()
                    } else {
                        "Object".to_string()
                    }
                } else {
                    ident.name.clone()
                }
            }
            TypeKind::SelfType => {
                if let Some(ref name) = self.current_struct_name {
                    name.clone()
                } else {
                    "Object".to_string()
                }
            }
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
                format!("new {}[{}]", self.java_type(element), size)
            }
            TypeKind::Named(ident) => {
                if ident.name == "Self" {
                    if let Some(ref name) = self.current_struct_name {
                        format!("new {}()", name)
                    } else {
                        "null".to_string()
                    }
                } else {
                    format!("new {}()", ident.name)
                }
            }
            TypeKind::SelfType => {
                if let Some(ref name) = self.current_struct_name {
                    format!("new {}()", name)
                } else {
                    "null".to_string()
                }
            }
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

    /// Whether a type maps to Java `short`
    fn is_short_primitive(ty: &ParserType) -> bool {
        use crate::parser::{PrimitiveType, TypeKind};
        if let TypeKind::Primitive(p) = &ty.kind {
            matches!(p.to_native(), PrimitiveType::U16 | PrimitiveType::I16)
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

    /// Whether a type is an array of non-u8 primitives (e.g., u32[8], u64[4]).
    /// Used to detect variables that need `Arrays.fill(arr, 0)` for secure_zero.
    fn is_non_u8_array_type(ty: &ParserType) -> bool {
        use crate::parser::{PrimitiveType, TypeKind};
        let inner_ty = match &ty.kind {
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => inner.as_ref(),
            _ => ty,
        };
        match &inner_ty.kind {
            TypeKind::Array { element, .. }
            | TypeKind::Slice { element }
            | TypeKind::ArrayRef { element, .. } => {
                if let TypeKind::Primitive(p) = &element.kind {
                    !matches!(p.to_native(), PrimitiveType::U8 | PrimitiveType::I8)
                } else {
                    false
                }
            }
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

    /// Extract the underlying object identifier name, looking through Deref/Ref/Paren.
    fn extract_object_ident_name(expr: &Expr) -> Option<&str> {
        match &expr.kind {
            ExprKind::Ident(ident) => Some(&ident.name),
            ExprKind::Deref(inner)
            | ExprKind::Ref(inner)
            | ExprKind::MutRef(inner)
            | ExprKind::Paren(inner) => Self::extract_object_ident_name(inner),
            _ => None,
        }
    }

    /// Unwrap transparent expression wrappers (Deref, Ref, MutRef, Paren)
    /// to find the underlying expression for pattern matching.
    fn unwrap_transparent(expr: &Expr) -> &Expr {
        match &expr.kind {
            ExprKind::Deref(inner)
            | ExprKind::Ref(inner)
            | ExprKind::MutRef(inner)
            | ExprKind::Paren(inner) => Self::unwrap_transparent(inner),
            _ => expr,
        }
    }

    /// Check if an assignment target expression refers to a byte-typed location.
    /// Returns true if assigning to this target requires a `(byte)` cast on the value.
    fn target_is_byte(&self, target: &Expr) -> bool {
        match &target.kind {
            ExprKind::Ident(ident) => self.byte_vars.contains(&ident.name),
            ExprKind::Index { array, .. } => {
                // Check if the array is a known byte array variable
                if let Some(ident_name) = Self::extract_object_ident_name(array)
                    && self.byte_array_vars.contains(ident_name)
                {
                    return true;
                }
                // Unwrap derefs/refs/parens to find a Field expression
                let inner_array = Self::unwrap_transparent(array);
                if let ExprKind::Field { object, field } = &inner_array.kind {
                    // struct_field: check if the struct field is a byte array
                    if let Some(obj_name) = Self::extract_object_ident_name(object)
                        && let Some(struct_name) = self.var_types.get(obj_name)
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
                if let Some(obj_name) = Self::extract_object_ident_name(object)
                    && let Some(struct_name) = self.var_types.get(obj_name)
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

    /// Register byte type tracking and struct type tracking for function/method parameters.
    /// Also registers parameter names in `declared_vars` so that for-loop variable
    /// declarations don't shadow them (which is a compile error in Java).
    fn register_param_byte_types(&mut self, params: &[crate::parser::Param]) {
        for param in params {
            // Track declared variable names to avoid duplicate declarations in for loops
            self.declared_vars.insert(param.name.name.clone());

            if Self::is_byte_primitive(&param.ty) {
                self.byte_vars.insert(param.name.name.clone());
            } else if Self::is_byte_array_type(&param.ty) {
                self.byte_array_vars.insert(param.name.name.clone());
            }
            if Self::is_non_u8_array_type(&param.ty) {
                self.non_u8_array_vars.insert(param.name.name.clone());
            }
            // Also register struct types in var_types (looking through refs)
            Self::register_struct_type_for_param(&param.name.name, &param.ty, &mut self.var_types);
        }
    }

    /// Register a struct type mapping for a parameter, looking through reference wrappers.
    fn register_struct_type_for_param(
        param_name: &str,
        ty: &ParserType,
        var_types: &mut HashMap<String, String>,
    ) {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Named(ident) => {
                var_types.insert(param_name.to_string(), ident.name.clone());
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                Self::register_struct_type_for_param(param_name, inner, var_types);
            }
            TypeKind::SelfType => {
                // SelfType is handled by the caller which knows the struct name
            }
            _ => {}
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
        // Detect if this function was monomorphized from a method/generic
        // If the function name contains "__", the prefix is the struct name
        self.current_struct_name = Self::infer_self_type_name(&func.name.name);

        self.write_indent();
        // Return type
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!("static {} ", self.java_type(ret_ty)));
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
                self.java_type(&param.ty),
                param.name.name
            ));
        }

        self.write(") {\n");
        self.indent();
        // Save tracking state for this function scope.
        // Clone (not take) byte vars so that global constants remain visible.
        let saved_byte_vars = self.byte_vars.clone();
        let saved_byte_array_vars = self.byte_array_vars.clone();
        let saved_non_u8_array_vars = self.non_u8_array_vars.clone();
        let saved_var_types_func = self.var_types.clone();
        let saved_return_type = self.current_return_type.take();
        let saved_declared_vars = std::mem::take(&mut self.declared_vars);
        self.current_return_type = func.return_type.clone();
        self.register_param_byte_types(&func.params);
        self.generate_block(&func.body);
        self.byte_vars = saved_byte_vars;
        self.byte_array_vars = saved_byte_array_vars;
        self.non_u8_array_vars = saved_non_u8_array_vars;
        self.var_types = saved_var_types_func;
        self.current_return_type = saved_return_type;
        self.declared_vars = saved_declared_vars;
        self.current_struct_name = None;
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_method(&mut self, struct_name: &str, func: &Function) {
        self.current_struct_name = Some(struct_name.to_string());
        let mangled_name = format!("{}__{}", struct_name, func.name.name);
        self.write_indent();
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!("static {} ", self.java_type(ret_ty)));
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
                self.java_type(&param.ty),
                param.name.name
            ));
        }

        self.write(") {\n");
        self.indent();
        let saved_byte_vars = self.byte_vars.clone();
        let saved_byte_array_vars = self.byte_array_vars.clone();
        let saved_non_u8_array_vars = self.non_u8_array_vars.clone();
        let saved_var_types_method = self.var_types.clone();
        let saved_return_type = self.current_return_type.take();
        let saved_declared_vars = std::mem::take(&mut self.declared_vars);
        self.current_return_type = func.return_type.clone();
        self.register_param_byte_types(&func.params);
        // For methods, register the self/receiver parameter (usually first) with the struct type
        // so that field accesses like self.block[i] can be resolved.
        if let Some(first_param) = func.params.first()
            && matches!(
                &first_param.ty.kind,
                crate::parser::TypeKind::SelfType
                    | crate::parser::TypeKind::MutRef(_)
                    | crate::parser::TypeKind::Ref(_)
            )
        {
            self.var_types
                .insert(first_param.name.name.clone(), struct_name.to_string());
        }
        self.generate_block(&func.body);
        self.byte_vars = saved_byte_vars;
        self.byte_array_vars = saved_byte_array_vars;
        self.non_u8_array_vars = saved_non_u8_array_vars;
        self.var_types = saved_var_types_method;
        self.current_return_type = saved_return_type;
        self.declared_vars = saved_declared_vars;
        self.current_struct_name = None;
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("static void test_{}() {{", test.name.name));
        self.indent();
        let saved_byte_vars = self.byte_vars.clone();
        let saved_byte_array_vars = self.byte_array_vars.clone();
        let saved_non_u8_array_vars = self.non_u8_array_vars.clone();
        let saved_return_type = self.current_return_type.take();
        let saved_declared_vars = std::mem::take(&mut self.declared_vars);
        self.generate_block(&test.body);
        self.byte_vars = saved_byte_vars;
        self.byte_array_vars = saved_byte_array_vars;
        self.non_u8_array_vars = saved_non_u8_array_vars;
        self.current_return_type = saved_return_type;
        self.declared_vars = saved_declared_vars;
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        // Track byte/byte-array constants for cast/comparison handling
        if Self::is_byte_primitive(&c.ty) {
            self.byte_vars.insert(c.name.name.clone());
        } else if Self::is_byte_array_type(&c.ty) {
            self.byte_array_vars.insert(c.name.name.clone());
        }
        self.write_indent();
        let needs_byte_cast =
            Self::is_byte_primitive(&c.ty) && Self::expr_may_widen_to_int(&c.value);
        let needs_short_cast = !needs_byte_cast
            && Self::is_short_primitive(&c.ty)
            && Self::expr_may_widen_to_int(&c.value);
        self.write(&format!(
            "static final {} {} = ",
            self.java_type(&c.ty),
            c.name.name
        ));
        if needs_byte_cast {
            self.write("(byte)(");
            self.generate_expr(&c.value);
            self.write(")");
        } else if needs_short_cast {
            self.write("(short)(");
            self.generate_expr(&c.value);
            self.write(")");
        } else {
            self.generate_expr_with_type_hint(&c.value, Some(&c.ty));
        }
        self.write(";\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        self.writeln(&format!("static class {} {{", s.name.name));
        self.indent();
        for field in &s.fields {
            let jt = self.java_type(&field.ty);
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
            let jt = self.java_type(&field.ty);
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
                    // Track non-u8 array variables for secure_zero -> Arrays.fill
                    if Self::is_non_u8_array_type(ty) {
                        self.non_u8_array_vars.insert(name.name.clone());
                    }
                }
                // Also infer byte array type from init expression when no
                // explicit type is given: [0u8; n], hex literals, bytes
                // literals, and byte array literals all produce byte[].
                if ty.is_none()
                    && let Some(init_expr) = init
                {
                    // Unwrap Ref/MutRef to get the actual expression
                    let unwrapped = match &init_expr.kind {
                        ExprKind::Ref(inner) | ExprKind::MutRef(inner) => inner.as_ref(),
                        _ => init_expr,
                    };
                    let inferred = self.infer_java_type(unwrapped);
                    if inferred == "byte[]" {
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

                // Track variable name as declared (for for-loop shadowing avoidance)
                self.declared_vars.insert(name.name.clone());

                self.write_indent();
                // Determine Java type
                let needs_byte_cast = ty.as_ref().is_some_and(Self::is_byte_primitive);
                let needs_short_cast =
                    !needs_byte_cast && ty.as_ref().is_some_and(Self::is_short_primitive);
                if let Some(ty) = ty {
                    self.write(&format!("{} {} = ", self.java_type(ty), name.name));
                    if let Some(init) = init {
                        if needs_byte_cast && Self::expr_may_widen_to_int(init) {
                            self.write("(byte)(");
                            self.generate_expr(init);
                            self.write(")");
                        } else if needs_short_cast && Self::expr_may_widen_to_int(init) {
                            self.write("(short)(");
                            self.generate_expr(init);
                            self.write(")");
                        } else {
                            self.generate_expr_with_type_hint(init, Some(ty));
                        }
                    } else {
                        self.write(&self.default_value_for_type(ty));
                    }
                } else if let Some(init) = init {
                    // No explicit type - infer from init expression
                    let inferred_type = self.infer_java_type(init);
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

                // In Java, a for-loop variable declared with `for (int i = ...)`
                // is in scope for the entire body. A nested for-loop using the same
                // variable name would cause "variable i is already defined".
                //
                // Strategy: if the variable is already declared (as a parameter,
                // let binding, or outer for-loop variable), just assign to it
                // without re-declaring. Otherwise, declare it with a type.
                //
                // Either way, we must track it as declared while processing the
                // body so that nested for-loops with the same name avoid re-declaring.
                let already_declared = self.declared_vars.contains(&var.name);

                // Rename the inner variable when it shadows an outer one.
                let java_var_name = if already_declared {
                    self.loop_var_counter += 1;
                    format!("{}__{}", var.name, self.loop_var_counter)
                } else {
                    var.name.clone()
                };
                // Track as declared so nested loops get renamed too.
                let was_new = self.declared_vars.insert(var.name.clone());
                let old_rename = if already_declared {
                    self.loop_var_renames
                        .insert(var.name.clone(), java_var_name.clone())
                } else {
                    None
                };

                self.write_indent();
                self.write(&format!("for ({} {} = ", type_str, java_var_name));
                if !use_long && !matches!(start.kind, ExprKind::Integer(_)) {
                    // Cast start to int in case the expression evaluates to long
                    // at runtime (e.g., a variable initialized from a function
                    // returning u64). Integer literals are already int-compatible.
                    self.write("(int)(");
                    self.generate_expr(start);
                    self.write(")");
                } else {
                    self.generate_expr(start);
                }
                self.write(&format!("; {} {} ", java_var_name, cmp));
                self.generate_expr(end);
                self.write(&format!("; {}++) {{\n", java_var_name));
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");

                // Restore state
                if already_declared {
                    match old_rename {
                        Some(prev) => {
                            self.loop_var_renames.insert(var.name.clone(), prev);
                        }
                        None => {
                            self.loop_var_renames.remove(&var.name);
                        }
                    }
                }
                if was_new {
                    self.declared_vars.remove(&var.name);
                }
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
                    // Check if we need a byte cast for the return value
                    let needs_byte_cast = self
                        .current_return_type
                        .as_ref()
                        .is_some_and(Self::is_byte_primitive)
                        && Self::expr_may_widen_to_int(expr);
                    let needs_short_cast = !needs_byte_cast
                        && self
                            .current_return_type
                            .as_ref()
                            .is_some_and(Self::is_short_primitive)
                        && Self::expr_may_widen_to_int(expr);
                    if needs_byte_cast {
                        self.write("return (byte)(");
                        self.generate_expr(expr);
                        self.write(");\n");
                    } else if needs_short_cast {
                        self.write("return (short)(");
                        self.generate_expr(expr);
                        self.write(");\n");
                    } else {
                        self.write("return ");
                        self.generate_expr(expr);
                        self.write(";\n");
                    }
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

    /// Generate an expression with an optional type hint from the declaration context.
    /// This ensures array literals match the declared element type (byte[] vs int[]).
    fn generate_expr_with_type_hint(&mut self, expr: &Expr, type_hint: Option<&ParserType>) {
        use crate::parser::TypeKind;
        if let Some(ty) = type_hint {
            // Unwrap Ref/MutRef wrappers so that `&[u8]` and `&mut [u8]` are
            // treated the same as `[u8]` for array type matching.
            let inner_ty = match &ty.kind {
                TypeKind::MutRef(inner) | TypeKind::Ref(inner) => inner.as_ref(),
                _ => ty,
            };
            // Also unwrap the expression through Ref/MutRef
            let inner_expr = match &expr.kind {
                ExprKind::Ref(inner) | ExprKind::MutRef(inner) => inner.as_ref(),
                _ => expr,
            };
            match (&inner_expr.kind, &inner_ty.kind) {
                // Array literal with a declared array type - use the declared element type
                (
                    ExprKind::Array(elements),
                    TypeKind::Array { element, .. }
                    | TypeKind::Slice { element }
                    | TypeKind::ArrayRef { element, .. },
                ) => {
                    let is_byte_el = Self::is_byte_primitive(element);
                    if elements.is_empty() {
                        if is_byte_el {
                            self.write("new byte[0]");
                        } else {
                            self.write(&format!("new {}[0]", self.java_type(element)));
                        }
                    } else if is_byte_el {
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
                        let elem_type = self.java_type(element);
                        self.write(&format!("new {}[]{{", elem_type));
                        for (i, elem) in elements.iter().enumerate() {
                            if i > 0 {
                                self.write(", ");
                            }
                            self.generate_expr(elem);
                        }
                        self.write("}");
                    }
                    return;
                }
                // ArrayRepeat with a declared array type
                (
                    ExprKind::ArrayRepeat { value, count },
                    TypeKind::Array { element, .. }
                    | TypeKind::Slice { element }
                    | TypeKind::ArrayRef { element, .. },
                ) => {
                    let is_byte_el = Self::is_byte_primitive(element);
                    if is_byte_el {
                        self.write("new byte[(int)(");
                        self.generate_expr(count);
                        self.write(")]");
                    } else {
                        let elem_type = self.java_type(element);
                        self.write(&format!("new {}[(int)(", elem_type));
                        self.generate_expr(count);
                        self.write(")]");
                    }
                    if !matches!(value.kind, ExprKind::Integer(0)) {
                        self.write(" /* fill: ");
                        self.generate_expr(value);
                        self.write(" */");
                    }
                    return;
                }
                _ => {}
            }
        }
        self.generate_expr(expr);
    }

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                // Integers that fit in int use plain literals.
                // Values > i32::MAX but <= u32::MAX represent unsigned 32-bit
                // values: emit (int)valueL which reinterprets the bits as signed
                // int (e.g., 0xFFFFFFFF -> -1). This avoids lossy conversion
                // errors in int context while auto-widening harmlessly in long
                // context.
                // Values > u32::MAX truly need long.
                if *n > u32::MAX as u128 {
                    self.write(&format!("{}L", n));
                } else if *n > i32::MAX as u128 {
                    self.write(&format!("(int){}L", n));
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
                // Use renamed loop variable if applicable
                if let Some(renamed) = self.loop_var_renames.get(&ident.name).cloned() {
                    self.write(&renamed);
                } else {
                    self.write(&ident.name);
                }
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

                // When comparing byte values with integer values, Java's signed
                // byte semantics cause issues: byte 0x89 is -119, not 137.
                // Mask byte operands with & 0xFF for unsigned comparison.
                let is_comparison = matches!(
                    op,
                    BinaryOp::Eq
                        | BinaryOp::Ne
                        | BinaryOp::Lt
                        | BinaryOp::Le
                        | BinaryOp::Gt
                        | BinaryOp::Ge
                );
                let left_is_byte = is_comparison && self.expr_produces_byte(left);
                let right_is_byte = is_comparison && self.expr_produces_byte(right);
                self.write("(");
                if left_is_byte {
                    self.write("(");
                    self.generate_expr(left);
                    self.write(" & 0xFF)");
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
                if right_is_byte {
                    self.write("(");
                    self.generate_expr(right);
                    self.write(" & 0xFF)");
                } else {
                    self.generate_expr(right);
                }
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
                if self.expr_produces_byte(index) {
                    // Byte values in Java are signed (-128..127). When used as
                    // an array index, they must be masked with & 0xFF to get the
                    // unsigned value (0..255), otherwise negative bytes produce
                    // negative indices causing ArrayIndexOutOfBoundsException.
                    self.write("(");
                    self.generate_expr(index);
                    self.write(" & 0xFF)");
                } else {
                    self.write("(int)(");
                    self.generate_expr(index);
                    self.write(")");
                }
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
                        let method_param_types =
                            self.func_param_types.get(mangled_name.as_str()).cloned();
                        self.write(&format!("{}(", mangled_name));
                        self.generate_expr(object);
                        for (arg_idx, arg) in args.iter().enumerate() {
                            self.write(", ");
                            // Parameter index is arg_idx + 1 because first param is self/receiver
                            let type_hint = method_param_types
                                .as_ref()
                                .and_then(|types| types.get(arg_idx + 1));
                            if let Some(ty) = type_hint {
                                if Self::is_byte_primitive(ty) && !Self::expr_is_already_byte(arg) {
                                    self.write("(byte)(");
                                    self.generate_expr(arg);
                                    self.write(")");
                                } else {
                                    self.generate_expr_with_type_hint(arg, Some(ty));
                                }
                            } else {
                                self.generate_expr(arg);
                            }
                        }
                        self.write(")");
                        return;
                    }
                }

                // Handle secure_zero calls on non-u8 arrays (e.g., int[])
                // secure_zero expects byte[] but state.h is int[].
                // Generate Arrays.fill(arr, 0) instead.
                if let ExprKind::Ident(ident) = &func.kind
                    && ident.name == "secure_zero"
                    && args.len() == 1
                {
                    // Unwrap &mut ref
                    let inner = match &args[0].kind {
                        ExprKind::MutRef(inner) | ExprKind::Ref(inner) => inner.as_ref(),
                        _ => &args[0],
                    };
                    if self.is_non_u8_array_expr(inner) {
                        self.write("java.util.Arrays.fill(");
                        self.generate_expr(inner);
                        self.write(", 0)");
                        return;
                    }
                }

                // Normal function call
                // Look up parameter types so we can generate correct array types
                let func_name = if let ExprKind::Ident(ident) = &func.kind {
                    Some(ident.name.clone())
                } else {
                    None
                };
                let param_types = func_name
                    .as_deref()
                    .and_then(|name| self.func_param_types.get(name))
                    .cloned();
                self.generate_expr(func);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    // Use type hint from parameter types if available
                    let type_hint = param_types.as_ref().and_then(|types| types.get(i));
                    if let Some(ty) = type_hint {
                        if Self::is_byte_primitive(ty) && !Self::expr_is_already_byte(arg) {
                            // Java method invocation context never allows
                            // narrowing conversion, so we must always add
                            // (byte) cast unless the expression already
                            // produces a byte value.
                            self.write("(byte)(");
                            self.generate_expr(arg);
                            self.write(")");
                        } else {
                            self.generate_expr_with_type_hint(arg, Some(ty));
                        }
                    } else {
                        self.generate_expr(arg);
                    }
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
                // Create a new struct instance and set fields using an IIFE lambda.
                // We avoid the anonymous subclass pattern `new T() {{ f = v; }}`
                // because when a field name matches a local variable name (e.g.,
                // `data = data;`), the field shadows the local variable inside the
                // anonymous class, causing the field to be assigned to itself (null).
                // The lambda pattern avoids this by using a unique temporary variable.
                // We use a depth counter (__s0, __s1, ...) to avoid shadowing when
                // struct literals are nested (Java lambdas cannot shadow enclosing vars).
                let depth = self.struct_lit_depth;
                self.struct_lit_depth += 1;
                let var_name = format!("__s{}", depth);
                self.write(&format!(
                    "((java.util.function.Supplier<{0}>)(() -> {{ {0} {1} = new {0}(); ",
                    name.name, var_name
                ));
                for (field_name, value) in fields {
                    self.write(&format!("{}.{} = ", var_name, field_name.name));
                    self.generate_expr(value);
                    self.write("; ");
                }
                self.write(&format!("return {}; }})).get()", var_name));
                self.struct_lit_depth -= 1;
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
                let method_param_types = self.func_param_types.get(mangled_name.as_str()).cloned();
                self.write(&format!("{}(", mangled_name));
                self.generate_expr(receiver);
                for (arg_idx, arg) in args.iter().enumerate() {
                    self.write(", ");
                    // Parameter index is arg_idx + 1 because first param is self/receiver
                    let type_hint = method_param_types
                        .as_ref()
                        .and_then(|types| types.get(arg_idx + 1));
                    if let Some(ty) = type_hint {
                        if Self::is_byte_primitive(ty) && Self::expr_may_widen_to_int(arg) {
                            self.write("(byte)(");
                            self.generate_expr(arg);
                            self.write(")");
                        } else {
                            self.generate_expr_with_type_hint(arg, Some(ty));
                        }
                    } else {
                        self.generate_expr(arg);
                    }
                }
                self.write(")");
            }
            ExprKind::TypeStaticCall {
                type_name,
                method_name,
                args,
            } => {
                let mangled = format!("{}__{}", type_name.name, method_name.name);
                let static_param_types = self.func_param_types.get(mangled.as_str()).cloned();
                self.write(&mangled);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    let type_hint = static_param_types.as_ref().and_then(|types| types.get(i));
                    if let Some(ty) = type_hint {
                        if Self::is_byte_primitive(ty) && Self::expr_may_widen_to_int(arg) {
                            self.write("(byte)(");
                            self.generate_expr(arg);
                            self.write(")");
                        } else {
                            self.generate_expr_with_type_hint(arg, Some(ty));
                        }
                    } else {
                        self.generate_expr(arg);
                    }
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
                            self.write(
                                "((java.util.function.Supplier<Integer>)(() -> { byte[] __b = ",
                            );
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
                // When widening from a byte-producing expression to a wider
                // unsigned type, mask with & 0xFF to get unsigned semantics.
                // Java bytes are signed (-128..127), so (int)byte sign-extends,
                // but AlgoC u8-to-u32 casts expect zero-extension.
                let source_is_byte = self.expr_produces_byte(expr);
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => {
                        self.write("((byte)(");
                        self.generate_expr(expr);
                        self.write("))");
                    }
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        if source_is_byte {
                            self.write("((short)(");
                            self.generate_expr(expr);
                            self.write(" & 0xFF))");
                        } else {
                            self.write("((short)(");
                            self.generate_expr(expr);
                            self.write("))");
                        }
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        if source_is_byte {
                            self.write("(");
                            self.generate_expr(expr);
                            self.write(" & 0xFF)");
                        } else {
                            self.write("((int)(");
                            self.generate_expr(expr);
                            self.write("))");
                        }
                    }
                    PrimitiveType::U64
                    | PrimitiveType::I64
                    | PrimitiveType::U128
                    | PrimitiveType::I128 => {
                        if source_is_byte {
                            self.write("((long)(");
                            self.generate_expr(expr);
                            self.write(" & 0xFF))");
                        } else {
                            self.write("((long)(");
                            self.generate_expr(expr);
                            self.write("))");
                        }
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
            // Method calls - also produce int typically
            ExprKind::MethodCall { .. } => true,
            // Type-qualified static calls and generic calls also produce int
            ExprKind::TypeStaticCall { .. } => true,
            ExprKind::GenericCall { .. } => true,
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

    /// Check whether an expression is already known to produce a Java `byte` value.
    /// Used to avoid redundant `(byte)` casts in method invocation context.
    fn expr_is_already_byte(expr: &Expr) -> bool {
        match &expr.kind {
            // An explicit cast to u8/i8 already produces byte
            ExprKind::Cast { ty, .. } => {
                if let crate::parser::TypeKind::Primitive(p) = &ty.kind {
                    matches!(
                        p.to_native(),
                        crate::parser::PrimitiveType::U8 | crate::parser::PrimitiveType::I8
                    )
                } else {
                    false
                }
            }
            // Parenthesized - check inner
            ExprKind::Paren(inner) => Self::expr_is_already_byte(inner),
            _ => false,
        }
    }

    /// Check if an expression refers to a non-u8 array (e.g., state.h where h: [u32; 8]).
    /// Used to detect secure_zero calls on non-u8 arrays that need special handling.
    fn is_non_u8_array_expr(&self, expr: &Expr) -> bool {
        use crate::parser::TypeKind;
        match &expr.kind {
            ExprKind::Field { object, field } => {
                if let Some(obj_name) = Self::extract_object_ident_name(object)
                    && let Some(struct_name) = self.var_types.get(obj_name)
                    && let Some(fields) = self.struct_defs.get(struct_name)
                {
                    for f in fields {
                        if f.name == field.name
                            && let TypeKind::Array { element, .. } = &f.ty.kind
                            && let TypeKind::Primitive(p) = &element.kind
                        {
                            return p.to_native() != crate::parser::PrimitiveType::U8;
                        }
                    }
                }
                false
            }
            ExprKind::Ident(ident) => self.non_u8_array_vars.contains(&ident.name),
            _ => false,
        }
    }

    /// Check if an expression produces a Java `byte` value.
    /// This is important for array indexing: byte is signed in Java (-128..127),
    /// so using it directly as an index can produce negative indices.
    fn expr_produces_byte(&self, expr: &Expr) -> bool {
        match &expr.kind {
            // Array index on a byte array produces byte
            ExprKind::Index { array, .. } => {
                if let Some(ident_name) = Self::extract_object_ident_name(array)
                    && self.byte_array_vars.contains(ident_name)
                {
                    return true;
                }
                // Check struct field byte arrays (including &[u8], &mut [u8], etc.)
                if let ExprKind::Field { object, field } = &array.kind
                    && let ExprKind::Ident(obj_ident) = &object.kind
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
            }
            // A variable declared as byte
            ExprKind::Ident(ident) => self.byte_vars.contains(&ident.name),
            // An explicit cast to byte
            ExprKind::Cast { ty, .. } => Self::is_byte_primitive(ty),
            // A field that is byte type
            ExprKind::Field { object, field } => {
                if let ExprKind::Ident(obj_ident) = &object.kind
                    && let Some(struct_name) = self.var_types.get(&obj_ident.name)
                    && let Some(fields) = self.struct_defs.get(struct_name)
                {
                    for f in fields {
                        if f.name == field.name {
                            return Self::is_byte_primitive(&f.ty);
                        }
                    }
                }
                false
            }
            ExprKind::Paren(inner) => self.expr_produces_byte(inner),
            _ => false,
        }
    }

    /// Infer the Java type string for an expression that has no explicit type annotation.
    fn infer_java_type(&self, expr: &Expr) -> String {
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
            ExprKind::Cast { ty, .. } => self.java_type(ty),
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
            ExprKind::Paren(inner) => self.infer_java_type(inner),
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

    /// Infer the concrete type name that should replace `Self` in a function.
    /// For functions with names like "StructName__method", the prefix is the struct name.
    fn infer_self_type_name(func_name: &str) -> Option<String> {
        if let Some(idx) = func_name.find("__") {
            return Some(func_name[..idx].to_string());
        }
        None
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
        self.non_u8_array_vars.clear();
        self.func_param_types.clear();
        self.current_return_type = None;
        self.declared_vars.clear();

        // Pre-pass: collect struct definitions, methods, and function parameter types
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
                        // Collect parameter types for method calls
                        let param_types: Vec<ParserType> =
                            method.params.iter().map(|p| p.ty.clone()).collect();
                        self.func_param_types.insert(mangled, param_types);
                    }
                    self.struct_methods
                        .insert(impl_def.target.name.clone(), methods);
                }
                ItemKind::Function(func) => {
                    let param_types: Vec<ParserType> =
                        func.params.iter().map(|p| p.ty.clone()).collect();
                    self.func_param_types
                        .insert(func.name.name.clone(), param_types);
                }
                ItemKind::Const(c) => {
                    // Track byte/byte-array constants in pre-pass so they're
                    // available for cast/comparison handling in all functions.
                    if Self::is_byte_primitive(&c.ty) {
                        self.byte_vars.insert(c.name.name.clone());
                    } else if Self::is_byte_array_type(&c.ty) {
                        self.byte_array_vars.insert(c.name.name.clone());
                    }
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
