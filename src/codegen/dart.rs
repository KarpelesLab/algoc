//! Dart code generator
//!
//! Generates Dart code from the analyzed AST.
//! Uses dart:typed_data for byte buffers and handles bitwise operations.
//! Dart int is always 64-bit on the VM, so we use masking for unsigned operations.

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

/// Dart code generator
pub struct DartGenerator {
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

impl DartGenerator {
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

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        self.writeln("// AlgoC Runtime Helpers");
        self.writeln("");

        // Reader class for streaming byte input
        self.writeln("class Reader {");
        self.indent();
        self.writeln("final Uint8List data;");
        self.writeln("int pos = 0;");
        self.writeln("late final ByteData view;");
        self.writeln("");
        self.writeln("Reader(this.data) {");
        self.indent();
        self.writeln("view = ByteData.sublistView(data);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u8
        self.writeln("int read_u8() {");
        self.indent();
        self.writeln("if (pos >= data.length) throw Exception('EOF');");
        self.writeln("return data[pos++];");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u16 variants
        self.writeln("int read_u16() => read_u16be();");
        self.writeln("int read_u16be() {");
        self.indent();
        self.writeln("if (pos + 2 > data.length) throw Exception('EOF');");
        self.writeln("final v = view.getUint16(pos, Endian.big);");
        self.writeln("pos += 2;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("int read_u16le() {");
        self.indent();
        self.writeln("if (pos + 2 > data.length) throw Exception('EOF');");
        self.writeln("final v = view.getUint16(pos, Endian.little);");
        self.writeln("pos += 2;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u32 variants
        self.writeln("int read_u32() => read_u32be();");
        self.writeln("int read_u32be() {");
        self.indent();
        self.writeln("if (pos + 4 > data.length) throw Exception('EOF');");
        self.writeln("final v = view.getUint32(pos, Endian.big);");
        self.writeln("pos += 4;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("int read_u32le() {");
        self.indent();
        self.writeln("if (pos + 4 > data.length) throw Exception('EOF');");
        self.writeln("final v = view.getUint32(pos, Endian.little);");
        self.writeln("pos += 4;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u64 variants
        self.writeln("int read_u64() => read_u64be();");
        self.writeln("int read_u64be() {");
        self.indent();
        self.writeln("if (pos + 8 > data.length) throw Exception('EOF');");
        self.writeln("final v = view.getUint64(pos, Endian.big);");
        self.writeln("pos += 8;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("int read_u64le() {");
        self.indent();
        self.writeln("if (pos + 8 > data.length) throw Exception('EOF');");
        self.writeln("final v = view.getUint64(pos, Endian.little);");
        self.writeln("pos += 8;");
        self.writeln("return v;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_bytes
        self.writeln("Uint8List read_bytes(int count) {");
        self.indent();
        self.writeln("if (pos + count > data.length) throw Exception('EOF');");
        self.writeln("final result = Uint8List.sublistView(data, pos, pos + count);");
        self.writeln("pos += count;");
        self.writeln("return result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_chunk
        self.writeln("Uint8List read_chunk(int maxSize) {");
        self.indent();
        self.writeln("final remaining = data.length - pos;");
        self.writeln("final count = maxSize < remaining ? maxSize : remaining;");
        self.writeln("final result = Uint8List.sublistView(data, pos, pos + count);");
        self.writeln("pos += count;");
        self.writeln("return result;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // eof
        self.writeln("bool eof() => pos >= data.length;");

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer class for streaming byte output
        self.writeln("class Writer {");
        self.indent();
        self.writeln("final Uint8List data;");
        self.writeln("int pos = 0;");
        self.writeln("late final ByteData view;");
        self.writeln("");
        self.writeln("Writer(this.data) {");
        self.indent();
        self.writeln("view = ByteData.sublistView(data);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u8
        self.writeln("void write_u8(int v) {");
        self.indent();
        self.writeln("if (pos >= data.length) throw Exception('Buffer overflow');");
        self.writeln("data[pos++] = v & 0xFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u16 variants
        self.writeln("void write_u16(int v) => write_u16be(v);");
        self.writeln("void write_u16be(int v) {");
        self.indent();
        self.writeln("if (pos + 2 > data.length) throw Exception('Buffer overflow');");
        self.writeln("view.setUint16(pos, v, Endian.big);");
        self.writeln("pos += 2;");
        self.dedent();
        self.writeln("}");
        self.writeln("void write_u16le(int v) {");
        self.indent();
        self.writeln("if (pos + 2 > data.length) throw Exception('Buffer overflow');");
        self.writeln("view.setUint16(pos, v, Endian.little);");
        self.writeln("pos += 2;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u32 variants
        self.writeln("void write_u32(int v) => write_u32be(v);");
        self.writeln("void write_u32be(int v) {");
        self.indent();
        self.writeln("if (pos + 4 > data.length) throw Exception('Buffer overflow');");
        self.writeln("view.setUint32(pos, v, Endian.big);");
        self.writeln("pos += 4;");
        self.dedent();
        self.writeln("}");
        self.writeln("void write_u32le(int v) {");
        self.indent();
        self.writeln("if (pos + 4 > data.length) throw Exception('Buffer overflow');");
        self.writeln("view.setUint32(pos, v, Endian.little);");
        self.writeln("pos += 4;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u64 variants
        self.writeln("void write_u64(int v) => write_u64be(v);");
        self.writeln("void write_u64be(int v) {");
        self.indent();
        self.writeln("if (pos + 8 > data.length) throw Exception('Buffer overflow');");
        self.writeln("view.setUint64(pos, v, Endian.big);");
        self.writeln("pos += 8;");
        self.dedent();
        self.writeln("}");
        self.writeln("void write_u64le(int v) {");
        self.indent();
        self.writeln("if (pos + 8 > data.length) throw Exception('Buffer overflow');");
        self.writeln("view.setUint64(pos, v, Endian.little);");
        self.writeln("pos += 8;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_bytes
        self.writeln("void write_bytes(Uint8List bytes) {");
        self.indent();
        self.writeln("if (pos + bytes.length > data.length) throw Exception('Buffer overflow');");
        self.writeln("data.setRange(pos, pos + bytes.length, bytes);");
        self.writeln("pos += bytes.length;");
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

        self.writeln("int __test_failures = 0;");
        self.writeln("String __test_name = '';");
        self.writeln("");

        self.writeln("void __assert(bool condition) {");
        self.indent();
        self.writeln("if (!condition) {");
        self.indent();
        self.writeln("__test_failures++;");
        self.writeln("print('  ASSERTION FAILED in $__test_name');");
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

    fn generate_method(&mut self, struct_name: &str, func: &crate::parser::Function) {
        let mangled_name = format!("{}__{}", struct_name, func.name.name);
        let return_type = self.dart_return_type(func.return_type.as_ref());

        self.write_indent();
        self.write(&format!("{} {}(", return_type, mangled_name));
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            let ty = self.dart_type(&param.ty);
            self.write(&format!("{} {}", ty, param.name.name));
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
        self.write_indent();
        self.write(&format!("final {} = ", c.name.name));
        self.generate_expr(&c.value);
        self.write(";\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Generate a Dart class for the struct
        self.writeln(&format!("class {} {{", s.name.name));
        self.indent();
        for field in &s.fields {
            let ty = self.dart_type(&field.ty);
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{} {} = {};", ty, field.name.name, init));
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Also generate a factory function for compatibility
        self.writeln(&format!("{} create_{}() {{", s.name.name, s.name.name));
        self.indent();
        self.writeln(&format!("return {}();", s.name.name));
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs in Dart
        self.writeln(&format!("class {} {{", l.name.name));
        self.indent();
        for field in &l.fields {
            let ty = self.dart_type(&field.ty);
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{} {} = {};", ty, field.name.name, init));
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln(&format!("{} create_{}() {{", l.name.name, l.name.name));
        self.indent();
        self.writeln(&format!("return {}();", l.name.name));
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum as a class with a tag field and variant factory methods
        self.writeln(&format!("class {} {{", e.name.name));
        self.indent();
        self.writeln("final String tag;");
        self.writeln("final List<dynamic> values;");
        self.writeln("final Map<String, dynamic> fields;");
        self.writeln("");
        self.writeln(&format!(
            "{}(this.tag, {{this.values = const [], this.fields = const {{}}}});",
            e.name.name
        ));
        self.writeln("");

        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!(
                        "static {} get {} => {}('{}');",
                        e.name.name, variant.name.name, e.name.name, variant.name.name
                    ));
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    let params: Vec<String> = (0..types.len())
                        .map(|i| format!("dynamic v{}", i))
                        .collect();
                    let args: Vec<String> = (0..types.len()).map(|i| format!("v{}", i)).collect();
                    self.writeln(&format!(
                        "static {} {}({}) => {}('{}', values: [{}]);",
                        e.name.name,
                        variant.name.name,
                        params.join(", "),
                        e.name.name,
                        variant.name.name,
                        args.join(", ")
                    ));
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    let params: Vec<String> = fields
                        .iter()
                        .map(|f| format!("dynamic {}", f.name.name))
                        .collect();
                    let field_entries: Vec<String> = fields
                        .iter()
                        .map(|f| format!("'{}': {}", f.name.name, f.name.name))
                        .collect();
                    self.writeln(&format!(
                        "static {} {}({{{}}}) => {}('{}', fields: {{{}}});",
                        e.name.name,
                        variant.name.name,
                        params.join(", "),
                        e.name.name,
                        variant.name.name,
                        field_entries.join(", ")
                    ));
                }
            }
        }

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    #[allow(clippy::only_used_in_recursion)]
    fn dart_type(&self, ty: &crate::parser::Type) -> String {
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::Bool => "bool".to_string(),
                    PrimitiveType::U128 | PrimitiveType::I128 => "BigInt".to_string(),
                    _ => "int".to_string(),
                }
            }
            TypeKind::Array { element, size } => match &element.kind {
                TypeKind::Primitive(p) => match p {
                    PrimitiveType::U8 => format!("Uint8List /* {} */", size),
                    PrimitiveType::U16 | PrimitiveType::U16Be | PrimitiveType::U16Le => {
                        format!("Uint16List /* {} */", size)
                    }
                    PrimitiveType::U32 | PrimitiveType::U32Be | PrimitiveType::U32Le => {
                        format!("Uint32List /* {} */", size)
                    }
                    PrimitiveType::I8 => format!("Int8List /* {} */", size),
                    PrimitiveType::I16 | PrimitiveType::I16Be | PrimitiveType::I16Le => {
                        format!("Int16List /* {} */", size)
                    }
                    PrimitiveType::I32 | PrimitiveType::I32Be | PrimitiveType::I32Le => {
                        format!("Int32List /* {} */", size)
                    }
                    _ => format!("List<int> /* {} */", size),
                },
                _ => format!("List<dynamic> /* {} */", size),
            },
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                match &element.kind {
                    TypeKind::Primitive(p) => match p {
                        PrimitiveType::U8 => "Uint8List".to_string(),
                        _ => "List<int>".to_string(),
                    },
                    _ => "List<dynamic>".to_string(),
                }
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.dart_type(inner),
            TypeKind::Named(ident) => ident.name.clone(),
            TypeKind::SelfType => "dynamic".to_string(),
        }
    }

    fn dart_return_type(&self, ty: Option<&crate::parser::Type>) -> String {
        match ty {
            Some(t) => self.dart_type(t),
            None => "void".to_string(),
        }
    }

    fn default_value_for_type(&self, ty: &crate::parser::Type) -> String {
        #![allow(clippy::only_used_in_recursion)]
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::Bool => "false".to_string(),
                    PrimitiveType::U128 | PrimitiveType::I128 => "BigInt.zero".to_string(),
                    _ => "0".to_string(),
                }
            }
            TypeKind::Array { element, size } => match &element.kind {
                TypeKind::Primitive(p) => match p {
                    PrimitiveType::U8 => format!("Uint8List({})", size),
                    PrimitiveType::U16 | PrimitiveType::U16Be | PrimitiveType::U16Le => {
                        format!("Uint16List({})", size)
                    }
                    PrimitiveType::U32 | PrimitiveType::U32Be | PrimitiveType::U32Le => {
                        format!("Uint32List({})", size)
                    }
                    PrimitiveType::I8 => format!("Int8List({})", size),
                    PrimitiveType::I16 | PrimitiveType::I16Be | PrimitiveType::I16Le => {
                        format!("Int16List({})", size)
                    }
                    PrimitiveType::I32 | PrimitiveType::I32Be | PrimitiveType::I32Le => {
                        format!("Int32List({})", size)
                    }
                    _ => format!("List<int>.filled({}, 0)", size),
                },
                _ => format!("List<dynamic>.filled({}, null)", size),
            },
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                match &element.kind {
                    TypeKind::Primitive(p) => match p {
                        PrimitiveType::U8 => "Uint8List(0)".to_string(),
                        _ => "<int>[]".to_string(),
                    },
                    _ => "<dynamic>[]".to_string(),
                }
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.default_value_for_type(inner),
            TypeKind::Named(ident) => {
                format!("create_{}()", ident.name)
            }
            _ => "0".to_string(),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        let return_type = self.dart_return_type(func.return_type.as_ref());

        self.write_indent();
        self.write(&format!("{} {}(", return_type, func.name.name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            let ty = self.dart_type(&param.ty);
            self.write(&format!("{} {}", ty, param.name.name));
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

                self.write_indent();
                self.write(&format!("var {} = ", name.name));
                if let Some(init) = init {
                    self.generate_expr(init);
                } else if let Some(ty) = ty {
                    self.write(&self.default_value_for_type(ty));
                } else {
                    self.write("0");
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
                        && let ExprKind::Slice {
                            array, start, end, ..
                        } = &inner.kind
                    {
                        let little_endian = endian == crate::parser::Endianness::Little;
                        let endian_str = if little_endian {
                            "Endian.little"
                        } else {
                            "Endian.big"
                        };
                        let (setter, _byte_count) = match p.to_native() {
                            crate::parser::PrimitiveType::U16
                            | crate::parser::PrimitiveType::I16 => ("setUint16", 2),
                            crate::parser::PrimitiveType::U32
                            | crate::parser::PrimitiveType::I32 => ("setUint32", 4),
                            crate::parser::PrimitiveType::U64
                            | crate::parser::PrimitiveType::I64 => ("setUint64", 8),
                            _ => ("setUint32", 4),
                        };
                        self.write_indent();
                        self.write("(() { final __s = Uint8List.sublistView(");
                        self.generate_expr(array);
                        self.write(", ");
                        self.generate_expr(start);
                        self.write(", ");
                        self.generate_expr(end);
                        self.write(&format!("); ByteData.sublistView(__s).{}(0, ", setter));
                        self.generate_expr(value);
                        self.write(&format!(", {}); }})();\n", endian_str));
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
                    BinaryOp::Div => "~/=",
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
                self.write(&format!("for (var {} = ", var.name));
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
                // Dart int is 64-bit on VM. Values > 2^63-1 need special handling.
                if *n > i64::MAX as u128 {
                    // Use hex for large values
                    self.write(&format!("0x{:X}", n));
                } else {
                    self.write(&format!("{}", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // Convert string to Uint8List
                self.write(&format!(
                    "Uint8List.fromList(\"{}\".codeUnits)",
                    escape_dart_string(s)
                ));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!(
                    "Uint8List.fromList(\"{}\".codeUnits)",
                    escape_dart_string(s)
                ));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to Uint8List
                // Generate inline byte list
                let bytes: Vec<String> = h
                    .as_bytes()
                    .chunks(2)
                    .map(|pair| {
                        let hex_str = std::str::from_utf8(pair).unwrap_or("00");
                        format!("0x{}", hex_str)
                    })
                    .collect();
                self.write(&format!("Uint8List.fromList([{}])", bytes.join(", ")));
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
                    BinaryOp::Div => " ~/ ",
                    BinaryOp::Rem => " % ",
                    BinaryOp::BitAnd => " & ",
                    BinaryOp::BitOr => " | ",
                    BinaryOp::BitXor => " ^ ",
                    BinaryOp::Shl => " << ",
                    BinaryOp::Shr => " >>> ", // Unsigned right shift in Dart 2.14+
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
                // Dart: Use Uint8List.sublistView for typed data, .sublist for general
                // We'll use sublistView for maximum compatibility with typed arrays
                self.write("Uint8List.sublistView(");
                self.generate_expr(array);
                self.write(", ");
                self.generate_expr(start);
                self.write(", ");
                self.generate_expr(end);
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
                        // Convert .len() to .length
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
                        self.write("(() { ");
                        for field_info in &fields {
                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty)
                            {
                                self.write(&format!("{}.{} = ", var_ident.name, field_info.name));
                                self.generate_expr(object);
                                self.write(&format!(".{}(); ", read_method));
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
                            self.write("(() { ");
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
                            self.write("})()");
                            return;
                        }
                    }

                    // Reader/Writer method calls - pass through directly
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
                    self.write("Uint8List(0)");
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
                        self.write("Uint8List.fromList([");
                    } else if all_ints {
                        self.write("Uint32List.fromList([");
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
                let is_byte = is_byte_value(value);

                if is_byte {
                    // Uint8List filled with value
                    self.write("Uint8List(");
                    self.generate_expr(count);
                    self.write(")");
                    // Only add .fill if value is nonzero
                    if let ExprKind::Integer(n) = &value.kind {
                        if *n != 0 {
                            self.write("..fillRange(0, ");
                            self.generate_expr(count);
                            self.write(", ");
                            self.generate_expr(value);
                            self.write(")");
                        }
                        // else: Uint8List is already zero-initialized
                    } else {
                        self.write("..fillRange(0, ");
                        self.generate_expr(count);
                        self.write(", ");
                        self.generate_expr(value);
                        self.write(")");
                    }
                } else {
                    self.write("List<int>.filled(");
                    self.generate_expr(count);
                    self.write(", ");
                    self.generate_expr(value);
                    self.write(")");
                }
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in Dart - objects are by reference, primitives by value
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are no-ops in Dart
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
                // Generate struct literal: ClassName()..field1 = val1..field2 = val2
                self.write(&format!("({}()", name.name));
                for (field_name, value) in fields {
                    self.write(&format!("..{} = ", field_name.name));
                    self.generate_expr(value);
                }
                self.write(")");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // Dart ternary: condition ? then : else
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
                self.write("((__match) { ");
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write(" else ");
                    }
                    self.generate_pattern_match(&arm.pattern, "__match");
                    self.write(" { return ");
                    self.generate_expr(&arm.body);
                    self.write("; }");
                }
                // Add a final throw for exhaustiveness
                self.write(" throw Exception('No match'); })(");
                self.generate_expr(expr);
                self.write(")");
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
                    "if ((() {{ var {} = {}; return true; }})()",
                    ident.name, scrutinee
                ));
                self.write(")");
            }
            PatternKind::EnumVariant {
                enum_name: _,
                variant_name,
                bindings: _,
            } => {
                self.write(&format!(
                    "if ({}.tag == '{}')",
                    scrutinee, variant_name.name
                ));
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
                self.write(&format!("{} == ", scrutinee));
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(_) => self.write("true"),
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!("{}.tag == '{}'", scrutinee, variant_name.name));
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

    fn generate_cast(&mut self, expr: &Expr, ty: &crate::parser::Type) {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        // Check for endian byte conversions (byte slice/array to integer)
        if let TypeKind::Primitive(p) = &ty.kind {
            let endian = p.endianness();
            if endian != Endianness::Native {
                let little_endian = endian == Endianness::Little;
                let native = p.to_native();
                let endian_str = if little_endian {
                    "Endian.little"
                } else {
                    "Endian.big"
                };

                // Check if source is a slice/array (byte conversion)
                if is_byte_sequence_expr(expr) {
                    let getter = match native {
                        PrimitiveType::U16 | PrimitiveType::I16 => Some(("getUint16", 2)),
                        PrimitiveType::U32 | PrimitiveType::I32 => Some(("getUint32", 4)),
                        PrimitiveType::U64 | PrimitiveType::I64 => Some(("getUint64", 8)),
                        PrimitiveType::U128 | PrimitiveType::I128 => {
                            // Manual byte manipulation for 128-bit
                            self.write("(() { final __b = ");
                            self.generate_expr(expr);
                            if little_endian {
                                self.write("; var __v = BigInt.zero;");
                                self.write(" for (var __i = 15; __i >= 0; __i--) { __v = (__v << 8) | BigInt.from(__b[__i]); }");
                                self.write(" return __v; })()");
                            } else {
                                self.write("; var __v = BigInt.zero;");
                                self.write(" for (var __i = 0; __i < 16; __i++) { __v = (__v << 8) | BigInt.from(__b[__i]); }");
                                self.write(" return __v; })()");
                            }
                            return;
                        }
                        _ => None,
                    };

                    if let Some((getter_name, _byte_count)) = getter {
                        self.write("(() { final __b = ");
                        self.generate_expr(expr);
                        self.write(&format!(
                            "; return ByteData.sublistView(Uint8List.fromList(__b is List<int> ? __b : List<int>.from(__b))).{}(0, {}); }})()",
                            getter_name, endian_str
                        ));
                        return;
                    }
                }

                // Integer to integer with different endianness - just mask
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & 0xFF)");
                    }
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & 0xFFFF)");
                    }
                    PrimitiveType::U32 | PrimitiveType::I32 => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & 0xFFFFFFFF)");
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        // Dart int is 64-bit, masking to unsigned range
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & 0xFFFFFFFFFFFFFFFF)");
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
            let endian_str = if little_endian {
                "Endian.little"
            } else {
                "Endian.big"
            };

            if bits <= 64 {
                let setter = match bits {
                    16 => "setUint16",
                    64 => "setUint64",
                    _ => "setUint32",
                };

                self.write(&format!(
                    "(() {{ final __a = Uint8List({}); ByteData.sublistView(__a).{}(0, ",
                    size, setter
                ));
                self.generate_expr(expr);
                self.write(&format!(", {}); return __a; }})()", endian_str));
                return;
            } else {
                // 128-bit - manual byte manipulation
                let inner_expr = if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                    inner
                } else {
                    expr
                };

                self.write("(() { final __v = ");
                self.generate_expr(inner_expr);
                self.write(&format!("; final __a = Uint8List({});", size));
                if little_endian {
                    self.write(" var __tmp = __v;");
                    self.write(
                        " for (var __i = 0; __i < 16; __i++) { __a[__i] = (__tmp & BigInt.from(0xFF)).toInt(); __tmp = __tmp >> 8; }",
                    );
                } else {
                    self.write(" var __tmp = __v;");
                    self.write(
                        " for (var __i = 15; __i >= 0; __i--) { __a[__i] = (__tmp & BigInt.from(0xFF)).toInt(); __tmp = __tmp >> 8; }",
                    );
                }
                self.write(" return __a; })()");
                return;
            }
        }

        // Standard casts with masking for unsigned types
        match &ty.kind {
            TypeKind::Primitive(p) => match p {
                PrimitiveType::U8 | PrimitiveType::I8 => {
                    self.write("((");
                    self.generate_expr(expr);
                    self.write(") & 0xFF)");
                }
                PrimitiveType::U16 | PrimitiveType::I16 => {
                    self.write("((");
                    self.generate_expr(expr);
                    self.write(") & 0xFFFF)");
                }
                PrimitiveType::U32 | PrimitiveType::I32 => {
                    self.write("((");
                    self.generate_expr(expr);
                    self.write(") & 0xFFFFFFFF)");
                }
                PrimitiveType::U64 | PrimitiveType::I64 => {
                    // Dart int is 64-bit on VM
                    self.write("((");
                    self.generate_expr(expr);
                    self.write(") & 0xFFFFFFFFFFFFFFFF)");
                }
                PrimitiveType::U128 | PrimitiveType::I128 => {
                    // Need BigInt for 128-bit
                    self.write("BigInt.from(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::Bool => {
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(" != 0)");
                }
                _ => {
                    // Endian variants handled above
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

impl Default for DartGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for DartGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();

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

        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("");
        self.writeln("import 'dart:typed_data';");
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
            self.writeln("void runTests() {");
            self.indent();
            self.writeln("var __passed = 0;");
            self.writeln("var __failed = 0;");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("__test_name = '{}';", name));
                self.writeln("__test_failures = 0;");
                self.writeln("try {");
                self.indent();
                self.writeln(&format!("test_{}();", name));
                self.writeln("if (__test_failures == 0) {");
                self.indent();
                self.writeln(&format!("print('PASS: {}');", name));
                self.writeln("__passed++;");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("print('FAIL: {}');", name));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("} catch (e) {");
                self.indent();
                self.writeln(&format!("print('FAIL: {} - $e');", name));
                self.writeln("__failed++;");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("print('');");
            self.writeln("print('$__passed passed, $__failed failed');");
            self.dedent();
            self.writeln("}");
            self.writeln("");
        }

        // Generate main function
        if self.include_tests {
            self.writeln("void main() {");
            self.indent();
            self.writeln("runTests();");
            self.dedent();
            self.writeln("}");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "dart"
    }

    fn language_name(&self) -> &'static str {
        "Dart"
    }
}

fn escape_dart_string(s: &str) -> String {
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
