//! Swift code generator
//!
//! Generates Swift code from the analyzed AST.
//! Uses Swift's native unsigned integer types and overflow operators for wrapping arithmetic.

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

/// Swift code generator
pub struct SwiftGenerator {
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
    /// Set of names that are mutable parameters (inout)
    inout_params: std::collections::HashSet<String>,
}

impl SwiftGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            inout_params: std::collections::HashSet::new(),
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

    /// Map a parser type to Swift type string
    fn swift_type(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => self.swift_primitive_type(*p),
            TypeKind::Array { element, size } => {
                // Fixed-size arrays don't exist as a distinct type in Swift;
                // we represent them as [ElementType] with known size.
                format!("[{}] /* size {} */", self.swift_type(element), size)
            }
            TypeKind::Slice { element } => format!("[{}]", self.swift_type(element)),
            TypeKind::ArrayRef { element, .. } => {
                // inout [Element] for mutable array refs
                format!("[{}]", self.swift_type(element))
            }
            TypeKind::MutRef(inner) => {
                // Swift uses inout at the function parameter level only;
                // for variable declarations we just use the inner type.
                self.swift_type(inner)
            }
            TypeKind::Ref(inner) => self.swift_type(inner),
            TypeKind::Named(ident) => ident.name.clone(),
            TypeKind::SelfType => "Self".to_string(),
        }
    }

    /// Map a primitive type to its Swift equivalent
    fn swift_primitive_type(&self, p: crate::parser::PrimitiveType) -> String {
        use crate::parser::PrimitiveType;
        match p.to_native() {
            PrimitiveType::U8 | PrimitiveType::I8 => "UInt8".to_string(),
            PrimitiveType::U16 | PrimitiveType::I16 => "UInt16".to_string(),
            PrimitiveType::U32 | PrimitiveType::I32 => "UInt32".to_string(),
            PrimitiveType::U64 | PrimitiveType::I64 => "UInt64".to_string(),
            PrimitiveType::U128 | PrimitiveType::I128 => {
                // Swift doesn't have native u128; use a pair or fallback to UInt64
                // For now, use UInt64 as the best available approximation.
                "UInt64".to_string()
            }
            PrimitiveType::Bool => "Bool".to_string(),
            _ => "UInt32".to_string(),
        }
    }

    /// Get the Swift type name suitable for constructing / casting
    fn swift_cast_type(&self, p: crate::parser::PrimitiveType) -> String {
        self.swift_primitive_type(p)
    }

    /// Check if an identifier is a Swift keyword and needs escaping
    fn swift_safe_ident(name: &str) -> String {
        match name {
            "repeat" | "class" | "func" | "var" | "let" | "in" | "for" | "while" | "return"
            | "break" | "continue" | "self" | "Self" | "true" | "false" | "nil" | "is" | "as"
            | "default" | "where" | "case" | "switch" | "do" | "try" | "catch" | "throw"
            | "defer" | "guard" | "import" | "if" | "else" | "struct" | "enum" | "protocol"
            | "extension" | "typealias" | "associatedtype" | "init" | "deinit" | "subscript"
            | "operator" | "precedencegroup" | "static" | "override" | "private" | "public"
            | "internal" | "open" | "fileprivate" | "mutating" | "nonmutating" | "inout"
            | "throws" | "rethrows" | "super" | "Any" | "Type" => {
                format!("{}_", name)
            }
            _ => name.to_string(),
        }
    }

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        self.writeln("// AlgoC Runtime Helpers");
        self.writeln("import Foundation");
        self.writeln("");

        // Reader class for streaming byte input
        self.writeln("class Reader {");
        self.indent();
        self.writeln("var data: [UInt8]");
        self.writeln("var pos: Int = 0");
        self.writeln("");
        self.writeln("init(_ data: [UInt8]) {");
        self.indent();
        self.writeln("self.data = data");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u8
        self.writeln("func read_u8() -> UInt8 {");
        self.indent();
        self.writeln("if pos >= data.count { fatalError(\"EOF\") }");
        self.writeln("let v = data[pos]");
        self.writeln("pos += 1");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u16 variants
        self.writeln("func read_u16() -> UInt16 { return read_u16be() }");
        self.writeln("func read_u16be() -> UInt16 {");
        self.indent();
        self.writeln("if pos + 2 > data.count { fatalError(\"EOF\") }");
        self.writeln("let v = UInt16(data[pos]) << 8 | UInt16(data[pos + 1])");
        self.writeln("pos += 2");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("func read_u16le() -> UInt16 {");
        self.indent();
        self.writeln("if pos + 2 > data.count { fatalError(\"EOF\") }");
        self.writeln("let v = UInt16(data[pos]) | UInt16(data[pos + 1]) << 8");
        self.writeln("pos += 2");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u32 variants
        self.writeln("func read_u32() -> UInt32 { return read_u32be() }");
        self.writeln("func read_u32be() -> UInt32 {");
        self.indent();
        self.writeln("if pos + 4 > data.count { fatalError(\"EOF\") }");
        self.writeln(
            "let v = UInt32(data[pos]) << 24 | UInt32(data[pos + 1]) << 16 | UInt32(data[pos + 2]) << 8 | UInt32(data[pos + 3])",
        );
        self.writeln("pos += 4");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("func read_u32le() -> UInt32 {");
        self.indent();
        self.writeln("if pos + 4 > data.count { fatalError(\"EOF\") }");
        self.writeln(
            "let v = UInt32(data[pos]) | UInt32(data[pos + 1]) << 8 | UInt32(data[pos + 2]) << 16 | UInt32(data[pos + 3]) << 24",
        );
        self.writeln("pos += 4");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_u64 variants
        self.writeln("func read_u64() -> UInt64 { return read_u64be() }");
        self.writeln("func read_u64be() -> UInt64 {");
        self.indent();
        self.writeln("if pos + 8 > data.count { fatalError(\"EOF\") }");
        self.writeln("var v: UInt64 = 0");
        self.writeln("for i in 0..<8 { v = v << 8 | UInt64(data[pos + i]) }");
        self.writeln("pos += 8");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("func read_u64le() -> UInt64 {");
        self.indent();
        self.writeln("if pos + 8 > data.count { fatalError(\"EOF\") }");
        self.writeln("var v: UInt64 = 0");
        self.writeln("for i in 0..<8 { v = v | UInt64(data[pos + i]) << (i * 8) }");
        self.writeln("pos += 8");
        self.writeln("return v");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_bytes
        self.writeln("func read_bytes(_ count: Int) -> [UInt8] {");
        self.indent();
        self.writeln("if pos + count > data.count { fatalError(\"EOF\") }");
        self.writeln("let result = Array(data[pos..<(pos + count)])");
        self.writeln("pos += count");
        self.writeln("return result");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // read_chunk
        self.writeln("func read_chunk(_ maxSize: Int) -> [UInt8] {");
        self.indent();
        self.writeln("let remaining = data.count - pos");
        self.writeln("let count = min(maxSize, remaining)");
        self.writeln("let result = Array(data[pos..<(pos + count)])");
        self.writeln("pos += count");
        self.writeln("return result");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // eof
        self.writeln("func eof() -> Bool { return pos >= data.count }");

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer class for streaming byte output
        self.writeln("class Writer {");
        self.indent();
        self.writeln("var data: [UInt8]");
        self.writeln("var pos: Int = 0");
        self.writeln("");
        self.writeln("init(_ data: [UInt8]) {");
        self.indent();
        self.writeln("self.data = data");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u8
        self.writeln("func write_u8(_ v: UInt8) {");
        self.indent();
        self.writeln("if pos >= data.count { fatalError(\"Buffer overflow\") }");
        self.writeln("data[pos] = v");
        self.writeln("pos += 1");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u16 variants
        self.writeln("func write_u16(_ v: UInt16) { write_u16be(v) }");
        self.writeln("func write_u16be(_ v: UInt16) {");
        self.indent();
        self.writeln("if pos + 2 > data.count { fatalError(\"Buffer overflow\") }");
        self.writeln("data[pos] = UInt8(v >> 8)");
        self.writeln("data[pos + 1] = UInt8(v & 0xFF)");
        self.writeln("pos += 2");
        self.dedent();
        self.writeln("}");
        self.writeln("func write_u16le(_ v: UInt16) {");
        self.indent();
        self.writeln("if pos + 2 > data.count { fatalError(\"Buffer overflow\") }");
        self.writeln("data[pos] = UInt8(v & 0xFF)");
        self.writeln("data[pos + 1] = UInt8(v >> 8)");
        self.writeln("pos += 2");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u32 variants
        self.writeln("func write_u32(_ v: UInt32) { write_u32be(v) }");
        self.writeln("func write_u32be(_ v: UInt32) {");
        self.indent();
        self.writeln("if pos + 4 > data.count { fatalError(\"Buffer overflow\") }");
        self.writeln("data[pos] = UInt8(v >> 24)");
        self.writeln("data[pos + 1] = UInt8((v >> 16) & 0xFF)");
        self.writeln("data[pos + 2] = UInt8((v >> 8) & 0xFF)");
        self.writeln("data[pos + 3] = UInt8(v & 0xFF)");
        self.writeln("pos += 4");
        self.dedent();
        self.writeln("}");
        self.writeln("func write_u32le(_ v: UInt32) {");
        self.indent();
        self.writeln("if pos + 4 > data.count { fatalError(\"Buffer overflow\") }");
        self.writeln("data[pos] = UInt8(v & 0xFF)");
        self.writeln("data[pos + 1] = UInt8((v >> 8) & 0xFF)");
        self.writeln("data[pos + 2] = UInt8((v >> 16) & 0xFF)");
        self.writeln("data[pos + 3] = UInt8(v >> 24)");
        self.writeln("pos += 4");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_u64 variants
        self.writeln("func write_u64(_ v: UInt64) { write_u64be(v) }");
        self.writeln("func write_u64be(_ v: UInt64) {");
        self.indent();
        self.writeln("if pos + 8 > data.count { fatalError(\"Buffer overflow\") }");
        self.writeln("for i in 0..<8 { data[pos + i] = UInt8((v >> ((7 - i) * 8)) & 0xFF) }");
        self.writeln("pos += 8");
        self.dedent();
        self.writeln("}");
        self.writeln("func write_u64le(_ v: UInt64) {");
        self.indent();
        self.writeln("if pos + 8 > data.count { fatalError(\"Buffer overflow\") }");
        self.writeln("for i in 0..<8 { data[pos + i] = UInt8((v >> (i * 8)) & 0xFF) }");
        self.writeln("pos += 8");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // write_bytes
        self.writeln("func write_bytes(_ bytes: [UInt8]) {");
        self.indent();
        self.writeln("if pos + bytes.count > data.count { fatalError(\"Buffer overflow\") }");
        self.writeln("for i in 0..<bytes.count { data[pos + i] = bytes[i] }");
        self.writeln("pos += bytes.count");
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

        self.writeln("func __assert(_ condition: Bool) {");
        self.indent();
        self.writeln("if !condition {");
        self.indent();
        self.writeln("__test_failures += 1");
        self.writeln("print(\"  ASSERTION FAILED in \\(__test_name)\")");
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
        self.inout_params.clear();

        let mangled_name = format!("{}__{}", struct_name, func.name.name);

        self.write_indent();
        self.write(&format!("func {}(", mangled_name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            let safe_param = Self::swift_safe_ident(&param.name.name);
            let is_mutable_ref = self.is_mutable_ref_type(&param.ty);
            if is_mutable_ref {
                self.inout_params.insert(param.name.name.clone());
                self.write(&format!(
                    "_ {}: inout {}",
                    safe_param,
                    self.swift_inner_type(&param.ty)
                ));
            } else {
                self.write(&format!("_ {}: {}", safe_param, self.swift_type(&param.ty)));
            }
        }

        self.write(")");
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!(" -> {}", self.swift_type(ret_ty)));
        }
        self.write(" {\n");
        self.indent();

        // Shadow immutable array parameters as var so they can be subscript-assigned
        for param in &func.params {
            if !self.is_mutable_ref_type(&param.ty) && self.is_array_type(&param.ty) {
                let safe_param = Self::swift_safe_ident(&param.name.name);
                self.writeln(&format!("var {} = {}", safe_param, safe_param));
            }
        }

        self.generate_block(&func.body);

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.inout_params.clear();

        self.writeln(&format!("func test_{}() {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        // Try to provide a type annotation for the constant
        let type_str = self.swift_type(&c.ty);
        self.write(&format!(
            "let {}: {} = ",
            Self::swift_safe_ident(&c.name.name),
            type_str
        ));
        self.generate_expr(&c.value);
        self.write("\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        let safe_struct = Self::swift_safe_ident(&s.name.name);
        self.writeln(&format!("struct {} {{", safe_struct));
        self.indent();
        for field in &s.fields {
            let ty_str = self.swift_type(&field.ty);
            let init = self.default_value_for_type(&field.ty);
            let safe_field = Self::swift_safe_ident(&field.name.name);
            self.writeln(&format!("var {}: {} = {}", safe_field, ty_str, init));
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Generate a factory function matching the pattern used by the JS generator
        self.writeln(&format!(
            "func create_{}() -> {} {{",
            safe_struct, safe_struct
        ));
        self.indent();
        self.writeln(&format!("return {}()", safe_struct));
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        let safe_layout = Self::swift_safe_ident(&l.name.name);
        self.writeln(&format!("struct {} {{", safe_layout));
        self.indent();
        for field in &l.fields {
            let ty_str = self.swift_type(&field.ty);
            let init = self.default_value_for_type(&field.ty);
            let safe_field = Self::swift_safe_ident(&field.name.name);
            self.writeln(&format!("var {}: {} = {}", safe_field, ty_str, init));
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln(&format!(
            "func create_{}() -> {} {{",
            safe_layout, safe_layout
        ));
        self.indent();
        self.writeln(&format!("return {}()", safe_layout));
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Swift enums with associated values
        self.writeln(&format!("enum {} {{", e.name.name));
        self.indent();
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    self.writeln(&format!("case {}", variant.name.name));
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    let params: Vec<String> = types.iter().map(|t| self.swift_type(t)).collect();
                    self.writeln(&format!(
                        "case {}({})",
                        variant.name.name,
                        params.join(", ")
                    ));
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    let params: Vec<String> = fields
                        .iter()
                        .map(|f| format!("{}: {}", f.name.name, self.swift_type(&f.ty)))
                        .collect();
                    self.writeln(&format!(
                        "case {}({})",
                        variant.name.name,
                        params.join(", ")
                    ));
                }
            }
        }
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

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
            TypeKind::Array { element, size } => {
                let elem_type = self.swift_type(element);
                let init = self.default_value_for_type(element);
                format!("[{}](repeating: {}, count: {})", elem_type, init, size)
            }
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                // Empty array of the element type, e.g. [UInt8]()
                let elem_type = self.swift_type(element);
                format!("[{}]()", elem_type)
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.default_value_for_type(inner),
            TypeKind::Named(ident) => {
                format!("create_{}()", ident.name)
            }
            _ => "0".to_string(),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        self.inout_params.clear();

        let func_safe_name = Self::swift_safe_ident(&func.name.name);
        self.write_indent();
        self.write(&format!("func {}(", func_safe_name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            let safe_param = Self::swift_safe_ident(&param.name.name);
            let is_mutable_ref = self.is_mutable_ref_type(&param.ty);
            if is_mutable_ref {
                self.inout_params.insert(param.name.name.clone());
                self.write(&format!(
                    "_ {}: inout {}",
                    safe_param,
                    self.swift_inner_type(&param.ty)
                ));
            } else {
                self.write(&format!("_ {}: {}", safe_param, self.swift_type(&param.ty)));
            }
        }

        self.write(")");
        if let Some(ret_ty) = &func.return_type {
            self.write(&format!(" -> {}", self.swift_type(ret_ty)));
        }
        self.write(" {\n");
        self.indent();

        // Shadow immutable array parameters as var so they can be subscript-assigned
        for param in &func.params {
            if !self.is_mutable_ref_type(&param.ty) && self.is_array_type(&param.ty) {
                let safe_param = Self::swift_safe_ident(&param.name.name);
                self.writeln(&format!("var {} = {}", safe_param, safe_param));
            }
        }

        self.generate_block(&func.body);

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Check if a type is a mutable reference
    fn is_mutable_ref_type(&self, ty: &ParserType) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::MutRef(_) => true,
            TypeKind::ArrayRef { .. } => true, // Array refs are typically passed as inout
            _ => false,
        }
    }

    /// Check if a type is an array/slice type
    fn is_array_type(&self, ty: &ParserType) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Array { .. } | TypeKind::Slice { .. } => true,
            TypeKind::Ref(inner) => {
                matches!(inner.kind, TypeKind::Slice { .. } | TypeKind::Array { .. })
            }
            _ => false,
        }
    }

    /// Get the inner type of a reference/mutable reference type
    fn swift_inner_type(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.swift_type(inner),
            TypeKind::ArrayRef { element, .. } => format!("[{}]", self.swift_type(element)),
            _ => self.swift_type(ty),
        }
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
                init,
                mutable,
            } => {
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
                let keyword = if *mutable { "var" } else { "let" };
                let safe_name = Self::swift_safe_ident(&name.name);
                self.write(&format!("{} {}", keyword, safe_name));

                // Add type annotation if we have one
                if let Some(ty) = ty {
                    let type_str = self.swift_type(ty);
                    self.write(&format!(": {}", type_str));
                }

                self.write(" = ");
                if let Some(init) = init {
                    self.generate_expr(init);
                } else if let Some(ty) = ty {
                    self.write(&self.default_value_for_type(ty));
                } else {
                    self.write("0");
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
                        && let ExprKind::Slice { array, start, .. } = &inner.kind
                    {
                        // Generate endian write into byte slice
                        let little_endian = endian == crate::parser::Endianness::Little;
                        let native = p.to_native();
                        self.write_indent();
                        self.write("do { var __val = ");
                        // Cast value to appropriate type
                        let cast_type = self.swift_cast_type(native);
                        self.write(&format!("{}(truncatingIfNeeded: ", cast_type));
                        self.generate_expr(value);
                        self.write(")");
                        self.write("; ");

                        let byte_count = p.bit_width() / 8;
                        for i in 0..byte_count {
                            let shift = if little_endian {
                                i * 8
                            } else {
                                ((byte_count - 1) - i) * 8
                            };
                            self.write("");
                            self.generate_expr(array);
                            self.write("[Int(");
                            self.generate_expr(start);
                            self.write(&format!(") + {}] = UInt8(truncatingIfNeeded: __val", i));
                            if shift > 0 {
                                self.write(&format!(" >> {}", shift));
                            }
                            self.write("); ");
                        }
                        // suppress unused variable warning
                        self.write("_ = __val }");
                        self.write("\n");
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
                // Swift uses overflow operators for wrapping arithmetic
                let op_str = match op {
                    BinaryOp::Add => " &+= ",
                    BinaryOp::Sub => " &-= ",
                    BinaryOp::Mul => " &*= ",
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
                self.write(&format!("for {} in ", Self::swift_safe_ident(&var.name)));
                self.generate_expr(start);
                self.write(if *inclusive { "..." } else { "..<" });
                self.generate_expr(end);
                self.write(" {\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::While { condition, body } => {
                self.write_indent();
                self.write("while ");
                self.generate_expr(condition);
                self.write(" {\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::Loop { body } => {
                self.writeln("while true {");
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
                self.writeln("do {");
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
                // Convert string to [UInt8]
                self.write(&format!("Array(\"{}\".utf8)", escape_swift_string(s)));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("Array(\"{}\".utf8)", escape_swift_string(s)));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to [UInt8] literal
                let bytes: Vec<String> = h
                    .as_bytes()
                    .chunks(2)
                    .map(|chunk| {
                        let hex_str = std::str::from_utf8(chunk).unwrap_or("00");
                        format!("0x{}", hex_str)
                    })
                    .collect();
                self.write(&format!("[UInt8](arrayLiteral: {})", bytes.join(", ")));
            }
            ExprKind::Ident(ident) => {
                self.write(&Self::swift_safe_ident(&ident.name));
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
                    BinaryOp::Add => " &+ ",
                    BinaryOp::Sub => " &- ",
                    BinaryOp::Mul => " &* ",
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
                self.write("[Int(");
                self.generate_expr(index);
                self.write(")]");
            }
            ExprKind::Slice {
                array, start, end, ..
            } => {
                self.write("Array(");
                self.generate_expr(array);
                self.write("[Int(");
                self.generate_expr(start);
                self.write(")..<Int(");
                self.generate_expr(end);
                self.write(")])");
            }
            ExprKind::Field { object, field } => {
                self.generate_expr(object);
                self.write(&format!(".{}", Self::swift_safe_ident(&field.name)));
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
                        // Convert .len() to .count
                        self.generate_expr(object);
                        self.write(".count");
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
                        for field_info in &fields {
                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty)
                            {
                                self.write(&format!("{}.{} = ", var_ident.name, field_info.name));
                                self.generate_expr(object);
                                self.write(&format!(".{}(); ", read_method));
                            }
                        }
                        // Trim trailing semicolon-space if any
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
                        // Generate: StructName__method(&object, args...)
                        self.write(&format!("{}(", mangled_name));
                        // Pass self as inout if it's a mutable method
                        self.write(&format!("&{}", Self::swift_safe_ident(&obj_ident.name)));
                        for arg in args {
                            self.write(", ");
                            self.generate_expr(arg);
                        }
                        self.write(")");
                        return;
                    }
                }

                // Check if calling with arguments that need & for inout
                self.generate_expr(func);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    // Check if arg is a MutRef - pass as &
                    if let ExprKind::MutRef(inner) = &arg.kind {
                        self.write("&");
                        self.generate_expr(inner);
                    } else if let ExprKind::Ref(inner) = &arg.kind {
                        // Pass references directly (Swift handles pass-by-value for structs)
                        self.generate_expr(inner);
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
                    self.write("[UInt8]()");
                } else {
                    // Determine element type from first element
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
                // Determine type
                let elem_type = if is_byte_value(value) {
                    "UInt8"
                } else {
                    "UInt32"
                };
                self.write(&format!("[{}](repeating: ", elem_type));
                self.generate_expr(value);
                self.write(", count: Int(");
                self.generate_expr(count);
                self.write("))");
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) => {
                // In Swift, references are mostly transparent
                // For inout parameters, the & is added at the call site
                self.generate_expr(inner);
            }
            ExprKind::MutRef(inner) => {
                // Mutable references: the & is added at the call site for inout params
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are no-ops in Swift (inout is automatic)
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
                    self.write(&format!("{}: ", field_name.name));
                    self.generate_expr(value);
                }
                self.write(")");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // Swift ternary: condition ? then : else
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
                // Generate match as a closure that evaluates a switch
                // { () -> ResultType in let __match = expr; switch __match { case ...: return ... } }()
                self.write("({ () in let __match = ");
                self.generate_expr(expr);
                self.write("; switch __match { ");
                for arm in arms {
                    self.generate_pattern_match(&arm.pattern);
                    self.write(": return ");
                    self.generate_expr(&arm.body);
                    self.write("; ");
                }
                self.write("} })()");
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

    fn generate_pattern_match(&mut self, pattern: &crate::parser::Pattern) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("default");
            }
            PatternKind::Literal(lit_expr) => {
                self.write("case ");
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(ident) => {
                self.write(&format!("case let {}", ident.name));
            }
            PatternKind::EnumVariant {
                enum_name: _,
                variant_name,
                bindings,
            } => {
                self.write(&format!("case .{}", variant_name.name));
                if !bindings.is_empty() {
                    self.write("(");
                    for (i, binding) in bindings.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        match &binding.kind {
                            PatternKind::Ident(ident) => {
                                self.write(&format!("let {}", ident.name));
                            }
                            PatternKind::Wildcard => {
                                self.write("_");
                            }
                            _ => {
                                self.write("_");
                            }
                        }
                    }
                    self.write(")");
                }
            }
            PatternKind::Tuple(patterns) => {
                self.write("case (");
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    match &p.kind {
                        PatternKind::Ident(ident) => {
                            self.write(&format!("let {}", ident.name));
                        }
                        PatternKind::Wildcard => {
                            self.write("_");
                        }
                        _ => {
                            self.write("_");
                        }
                    }
                }
                self.write(")");
            }
            PatternKind::Or(patterns) => {
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    // In Swift, multiple case patterns are separated by commas
                    self.generate_pattern_match_inner(p);
                }
            }
        }
    }

    /// Generate the inner pattern (without the "case" prefix) for Or patterns
    fn generate_pattern_match_inner(&mut self, pattern: &crate::parser::Pattern) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => self.write("default"),
            PatternKind::Literal(lit_expr) => {
                self.write("case ");
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(ident) => self.write(&format!("case let {}", ident.name)),
            PatternKind::EnumVariant {
                variant_name,
                bindings,
                ..
            } => {
                self.write(&format!("case .{}", variant_name.name));
                if !bindings.is_empty() {
                    self.write("(");
                    for (i, binding) in bindings.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        match &binding.kind {
                            PatternKind::Ident(ident) => {
                                self.write(&format!("let {}", ident.name));
                            }
                            _ => self.write("_"),
                        }
                    }
                    self.write(")");
                }
            }
            PatternKind::Tuple(_) => self.write("default"),
            PatternKind::Or(patterns) => {
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_pattern_match_inner(p);
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

    fn generate_cast(&mut self, expr: &Expr, ty: &crate::parser::Type) {
        use crate::parser::{Endianness, PrimitiveType, TypeKind};

        // Check for endian byte conversions (byte slice/array to integer)
        if let TypeKind::Primitive(p) = &ty.kind {
            let endian = p.endianness();
            if endian != Endianness::Native {
                let little_endian = endian == Endianness::Little;
                let native = p.to_native();

                // Check if source is a slice/array (byte conversion)
                if is_byte_sequence_expr(expr) {
                    let cast_type = self.swift_cast_type(native);
                    let byte_count = p.bit_width() / 8;

                    // Generate manual byte-to-integer conversion
                    self.write("({ (__b: [UInt8]) -> ");
                    self.write(&cast_type);
                    self.write(" in var __v: ");
                    self.write(&cast_type);
                    self.write(" = 0; ");

                    for i in 0..byte_count {
                        let shift = if little_endian {
                            i * 8
                        } else {
                            ((byte_count - 1) - i) * 8
                        };
                        self.write(&format!("__v = __v | {}(", cast_type));
                        self.write(&format!("__b[{}])", i));
                        if shift > 0 {
                            self.write(&format!(" << {}", shift));
                        }
                        self.write("; ");
                    }
                    self.write("return __v })(");
                    self.generate_expr(expr);
                    self.write(")");
                    return;
                }

                // Integer to integer with different endianness - just truncate
                let cast_type = self.swift_cast_type(native);
                self.write(&format!("{}(truncatingIfNeeded: ", cast_type));
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
            let byte_count = *size;
            let inner_expr = if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                inner
            } else {
                expr
            };

            let source_type = match bits {
                16 => "UInt16",
                64 => "UInt64",
                128 => "UInt64", // Swift has no UInt128
                _ => "UInt32",
            };

            self.write(&format!(
                "{{ (__val: {}) -> [UInt8] in var __a = [UInt8](repeating: 0, count: {}); ",
                source_type, byte_count
            ));
            for i in 0..byte_count {
                let shift = if little_endian {
                    i * 8
                } else {
                    ((byte_count - 1) - i) * 8
                };
                self.write(&format!("__a[{}] = UInt8(truncatingIfNeeded: __val", i));
                if shift > 0 {
                    self.write(&format!(" >> {}", shift));
                }
                self.write("); ");
            }
            self.write("return __a }(");
            // Cast the source expression to the correct type
            self.write(&format!("{}(truncatingIfNeeded: ", source_type));
            self.generate_expr(inner_expr);
            self.write("))");
            return;
        }

        // Standard casts
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let cast_type = self.swift_cast_type(*p);
                match p.to_native() {
                    PrimitiveType::Bool => {
                        // Convert to bool: != 0
                        self.write("(");
                        self.generate_expr(expr);
                        self.write(" != 0)");
                    }
                    _ => {
                        // Use truncatingIfNeeded: for safe wrapping conversion
                        self.write(&format!("{}(truncatingIfNeeded: ", cast_type));
                        self.generate_expr(expr);
                        self.write(")");
                    }
                }
            }
            _ => {
                // Named type cast or other - just generate expression
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

fn escape_swift_string(s: &str) -> String {
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

impl Default for SwiftGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for SwiftGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();

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
            self.writeln("func run_tests() -> Bool {");
            self.indent();
            self.writeln("var __passed = 0");
            self.writeln("var __failed = 0");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("__test_name = \"{}\"", name));
                self.writeln("__test_failures = 0");
                self.writeln(&format!("test_{}()", name));
                self.writeln("if __test_failures == 0 {");
                self.indent();
                self.writeln(&format!("print(\"PASS: {}\")", name));
                self.writeln("__passed += 1");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("print(\"FAIL: {}\")", name));
                self.writeln("__failed += 1");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("print(\"\")");
            self.writeln("print(\"\\(__passed) passed, \\(__failed) failed\")");
            self.writeln("return __failed == 0");
            self.dedent();
            self.writeln("}");
            self.writeln("");

            // Auto-run tests when executed directly
            self.writeln("// Auto-run tests");
            self.writeln("import Foundation");
            self.writeln("exit(run_tests() ? 0 : 1)");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "swift"
    }

    fn language_name(&self) -> &'static str {
        "Swift"
    }
}
