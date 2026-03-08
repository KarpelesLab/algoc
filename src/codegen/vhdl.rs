//! VHDL code generator
//!
//! Generates VHDL code from the analyzed AST.
//! Uses sequential VHDL (inside processes/procedures/functions) to emulate
//! imperative behavior. The generated code is intended for simulation with GHDL,
//! not for hardware synthesis.

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
#[allow(dead_code)]
struct StructFieldInfo {
    name: String,
    ty: ParserType,
}

/// Struct method info (method name -> mangled function name)
type MethodMap = HashMap<String, String>;

/// VHDL code generator
pub struct VhdlGenerator {
    /// Current indentation level
    indent: usize,
    /// Output buffer
    output: String,
    /// Whether to include test functions and runner
    include_tests: bool,
    /// Struct definitions for record generation
    struct_defs: HashMap<String, Vec<StructFieldInfo>>,
    /// Struct methods: struct_name -> (method_name -> mangled_name)
    struct_methods: HashMap<String, MethodMap>,
    /// Variable types (for struct access)
    var_types: HashMap<String, String>,
    /// Known array type declarations we have already emitted
    array_type_decls: Vec<String>,
    /// Current function return type width (for return value sizing)
    current_return_width: Option<u32>,
}

impl VhdlGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            array_type_decls: Vec::new(),
            current_return_width: None,
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

    // --- Type helpers ---

    /// Map a parser type to a VHDL type string
    fn type_to_vhdl(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => self.primitive_to_vhdl(*p),
            TypeKind::Array { element, size } => {
                let elem = self.type_to_vhdl(element);
                format!("array_{}_{}", self.type_to_tag(element), size)
                    + &format!(" -- (array(0 to {}) of {})", size.saturating_sub(1), elem)
                        .chars()
                        .filter(|_| false) // suppress comment in type position
                        .collect::<String>()
            }
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                // Slices/array refs are modeled as unconstrained arrays
                format!("array_{}_natural", self.type_to_tag(element))
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                // References are transparent in VHDL simulation
                self.type_to_vhdl(inner)
            }
            TypeKind::Named(ident) => {
                // Record type
                format!("t_{}", ident.name)
            }
            TypeKind::SelfType => "t_self".to_string(),
        }
    }

    /// Get a short tag for a type (used in array type names)
    fn type_to_tag(&self, ty: &ParserType) -> String {
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                match native {
                    PrimitiveType::U8 | PrimitiveType::I8 => "u8".to_string(),
                    PrimitiveType::U16 | PrimitiveType::I16 => "u16".to_string(),
                    PrimitiveType::U32 | PrimitiveType::I32 => "u32".to_string(),
                    PrimitiveType::U64 | PrimitiveType::I64 => "u64".to_string(),
                    PrimitiveType::U128 | PrimitiveType::I128 => "u128".to_string(),
                    PrimitiveType::Bool => "bool".to_string(),
                    _ => "u32".to_string(),
                }
            }
            TypeKind::Named(ident) => ident.name.clone(),
            _ => "unknown".to_string(),
        }
    }

    /// Map a primitive type to VHDL
    fn primitive_to_vhdl(&self, p: crate::parser::PrimitiveType) -> String {
        use crate::parser::PrimitiveType;
        let native = p.to_native();
        match native {
            PrimitiveType::U8 => "unsigned(7 downto 0)".to_string(),
            PrimitiveType::I8 => "signed(7 downto 0)".to_string(),
            PrimitiveType::U16 => "unsigned(15 downto 0)".to_string(),
            PrimitiveType::I16 => "signed(15 downto 0)".to_string(),
            PrimitiveType::U32 => "unsigned(31 downto 0)".to_string(),
            PrimitiveType::I32 => "signed(31 downto 0)".to_string(),
            PrimitiveType::U64 => "unsigned(63 downto 0)".to_string(),
            PrimitiveType::I64 => "signed(63 downto 0)".to_string(),
            PrimitiveType::U128 => "unsigned(127 downto 0)".to_string(),
            PrimitiveType::I128 => "signed(127 downto 0)".to_string(),
            PrimitiveType::Bool => "boolean".to_string(),
            // Endian-qualified variants map to same widths
            _ => {
                let bits = p.bit_width();
                if p.is_signed() {
                    format!("signed({} downto 0)", bits - 1)
                } else {
                    format!("unsigned({} downto 0)", bits - 1)
                }
            }
        }
    }

    /// Get the bit width for a parser type (defaults to 32)
    fn type_bit_width(&self, ty: &ParserType) -> u32 {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => p.bit_width(),
            _ => 32,
        }
    }

    /// Check if a type is boolean
    fn is_bool_type(&self, ty: &ParserType) -> bool {
        use crate::parser::{PrimitiveType, TypeKind};
        matches!(&ty.kind, TypeKind::Primitive(PrimitiveType::Bool))
    }

    /// Get VHDL default value for a type
    #[allow(clippy::only_used_in_recursion)]
    fn default_value_for_type(&self, ty: &ParserType) -> String {
        use crate::parser::{PrimitiveType, TypeKind};
        match &ty.kind {
            TypeKind::Primitive(PrimitiveType::Bool) => "false".to_string(),
            TypeKind::Primitive(p) => {
                let bits = p.bit_width();
                if p.is_signed() {
                    format!("to_signed(0, {})", bits)
                } else {
                    format!("to_unsigned(0, {})", bits)
                }
            }
            TypeKind::Array { element, size } => {
                let elem_default = self.default_value_for_type(element);
                format!("(0 to {} => {})", size.saturating_sub(1), elem_default)
            }
            TypeKind::Named(_) => {
                // Record default - use an aggregate with all defaults
                // Simplified: just use (others => '0') which works for simple records
                "init_record".to_string()
            }
            _ => "(others => '0')".to_string(),
        }
    }

    /// Get the VHDL element type string for an array element
    fn element_type_vhdl(&self, element: &ParserType) -> String {
        self.type_to_vhdl(element)
    }

    // --- Code generation ---

    #[allow(dead_code)]
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
                self.writeln("-- Use statements are resolved at compile time");
            }
            ItemKind::Impl(impl_def) => {
                // Generate methods as standalone functions/procedures with mangled names
                for method in &impl_def.methods {
                    self.generate_method(&impl_def.target.name, method);
                }
            }
            ItemKind::Interface(_) => {
                self.writeln("-- Interfaces are compile-time only, no runtime representation");
            }
        }
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        self.writeln(&format!("type t_{} is record", s.name.name));
        self.indent();
        for field in &s.fields {
            let vhdl_ty = self.type_to_vhdl(&field.ty);
            self.writeln(&format!("{} : {};", field.name.name, vhdl_ty));
        }
        self.dedent();
        self.writeln("end record;");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts map to records in VHDL
        self.writeln(&format!("type t_{} is record", l.name.name));
        self.indent();
        for field in &l.fields {
            let vhdl_ty = self.type_to_vhdl(&field.ty);
            self.writeln(&format!("{} : {};", field.name.name, vhdl_ty));
        }
        self.dedent();
        self.writeln("end record;");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum as a VHDL enumeration type for unit variants
        // For variants with data, use a tagged record approach
        let has_data_variants = e
            .variants
            .iter()
            .any(|v| !matches!(v.data, crate::parser::EnumVariantData::Unit));

        if has_data_variants {
            // Complex enum with data: generate a tag type and a record
            self.writeln(&format!("-- Enum {} (with data variants)", e.name.name));
            self.write_indent();
            self.write(&format!("type t_{}_tag is (", e.name.name));
            for (i, variant) in e.variants.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(&format!("TAG_{}", variant.name.name.to_uppercase()));
            }
            self.write(");\n");
            self.writeln(&format!("type t_{} is record", e.name.name));
            self.indent();
            self.writeln(&format!("tag : t_{}_tag;", e.name.name));
            // Add fields for each data variant
            for variant in &e.variants {
                match &variant.data {
                    crate::parser::EnumVariantData::Tuple(types) => {
                        for (i, ty) in types.iter().enumerate() {
                            let vhdl_ty = self.type_to_vhdl(ty);
                            self.writeln(&format!(
                                "{}_v{} : {};",
                                variant.name.name.to_lowercase(),
                                i,
                                vhdl_ty
                            ));
                        }
                    }
                    crate::parser::EnumVariantData::Struct(fields) => {
                        for field in fields {
                            let vhdl_ty = self.type_to_vhdl(&field.ty);
                            self.writeln(&format!(
                                "{}_{} : {};",
                                variant.name.name.to_lowercase(),
                                field.name.name,
                                vhdl_ty
                            ));
                        }
                    }
                    crate::parser::EnumVariantData::Unit => {}
                }
            }
            self.dedent();
            self.writeln("end record;");
        } else {
            // Simple enum: all unit variants
            self.write_indent();
            self.write(&format!("type t_{} is (", e.name.name));
            for (i, variant) in e.variants.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(&format!("ENUM_{}", variant.name.name.to_uppercase()));
            }
            self.write(");\n");
        }
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        let vhdl_ty = self.type_to_vhdl(&c.ty);
        self.write(&format!("constant {} : {} := ", c.name.name, vhdl_ty));
        self.generate_expr(&c.value);
        self.write(";\n");
        self.writeln("");
    }

    fn generate_function(&mut self, func: &Function) {
        self.var_types.clear();

        let has_return = func.return_type.is_some();
        let is_void = !has_return;
        let ret_is_bool = func
            .return_type
            .as_ref()
            .is_some_and(|t| self.is_bool_type(t));

        // Track return width
        self.current_return_width = func.return_type.as_ref().map(|t| self.type_bit_width(t));

        if is_void {
            // Generate as procedure
            self.write_indent();
            self.write(&format!("procedure proc_{}", func.name.name));
            if !func.params.is_empty() {
                self.write("(");
                for (i, param) in func.params.iter().enumerate() {
                    if i > 0 {
                        self.write("; ");
                    }
                    let vhdl_ty = self.type_to_vhdl(&param.ty);
                    self.write(&format!("{} : inout {}", param.name.name, vhdl_ty));
                }
                self.write(")");
            }
            self.write(" is\n");
            self.indent();
            // Declare local variables from the body
            self.generate_local_declarations(&func.body);
            self.dedent();
            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln(&format!("end procedure proc_{};", func.name.name));
        } else {
            // Generate as function
            let ret_ty = func.return_type.as_ref().unwrap();
            let vhdl_ret = self.type_to_vhdl(ret_ty);

            self.write_indent();
            self.write(&format!("function func_{}", func.name.name));
            if !func.params.is_empty() {
                self.write("(");
                for (i, param) in func.params.iter().enumerate() {
                    if i > 0 {
                        self.write("; ");
                    }
                    let vhdl_ty = self.type_to_vhdl(&param.ty);
                    self.write(&format!("{} : {}", param.name.name, vhdl_ty));
                }
                self.write(")");
            }
            self.write(&format!(" return {} is\n", vhdl_ret));
            self.indent();
            // Declare result variable
            if ret_is_bool {
                self.writeln("variable v_result : boolean := false;");
            } else {
                let bits = self.type_bit_width(ret_ty);
                if self.is_signed_type(ret_ty) {
                    self.writeln(&format!(
                        "variable v_result : signed({} downto 0) := (others => '0');",
                        bits - 1
                    ));
                } else {
                    self.writeln(&format!(
                        "variable v_result : unsigned({} downto 0) := (others => '0');",
                        bits - 1
                    ));
                }
            }
            // Declare local variables from the body
            self.generate_local_declarations(&func.body);
            self.dedent();
            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.writeln("return v_result;");
            self.dedent();
            self.writeln(&format!("end function func_{};", func.name.name));
        }
        self.current_return_width = None;
        self.writeln("");
    }

    fn generate_method(&mut self, struct_name: &str, func: &Function) {
        self.var_types.clear();

        let mangled_name = format!("{}__{}", struct_name, func.name.name);
        let has_return = func.return_type.is_some();
        let is_void = !has_return;
        let ret_is_bool = func
            .return_type
            .as_ref()
            .is_some_and(|t| self.is_bool_type(t));

        self.current_return_width = func.return_type.as_ref().map(|t| self.type_bit_width(t));

        if is_void {
            self.write_indent();
            self.write(&format!("procedure proc_{}", mangled_name));
            if !func.params.is_empty() {
                self.write("(");
                for (i, param) in func.params.iter().enumerate() {
                    if i > 0 {
                        self.write("; ");
                    }
                    let vhdl_ty = self.type_to_vhdl(&param.ty);
                    self.write(&format!("{} : inout {}", param.name.name, vhdl_ty));
                }
                self.write(")");
            }
            self.write(" is\n");
            self.indent();
            self.generate_local_declarations(&func.body);
            self.dedent();
            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln(&format!("end procedure proc_{};", mangled_name));
        } else {
            let ret_ty = func.return_type.as_ref().unwrap();
            let vhdl_ret = self.type_to_vhdl(ret_ty);

            self.write_indent();
            self.write(&format!("function func_{}", mangled_name));
            if !func.params.is_empty() {
                self.write("(");
                for (i, param) in func.params.iter().enumerate() {
                    if i > 0 {
                        self.write("; ");
                    }
                    let vhdl_ty = self.type_to_vhdl(&param.ty);
                    self.write(&format!("{} : {}", param.name.name, vhdl_ty));
                }
                self.write(")");
            }
            self.write(&format!(" return {} is\n", vhdl_ret));
            self.indent();
            if ret_is_bool {
                self.writeln("variable v_result : boolean := false;");
            } else {
                let bits = self.type_bit_width(ret_ty);
                if self.is_signed_type(ret_ty) {
                    self.writeln(&format!(
                        "variable v_result : signed({} downto 0) := (others => '0');",
                        bits - 1
                    ));
                } else {
                    self.writeln(&format!(
                        "variable v_result : unsigned({} downto 0) := (others => '0');",
                        bits - 1
                    ));
                }
            }
            self.generate_local_declarations(&func.body);
            self.dedent();
            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.writeln("return v_result;");
            self.dedent();
            self.writeln(&format!("end function func_{};", mangled_name));
        }
        self.current_return_width = None;
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.var_types.clear();

        self.write_indent();
        self.write(&format!("procedure test_{}", test.name.name));
        self.write(" is\n");
        self.indent();
        self.generate_local_declarations(&test.body);
        self.dedent();
        self.writeln("begin");
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln(&format!("end procedure test_{};", test.name.name));
        self.writeln("");
    }

    /// Pre-scan a block for local variable declarations and emit them in the
    /// declarative region (before `begin`).
    fn generate_local_declarations(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.scan_and_declare_stmt(stmt);
        }
    }

    /// Recursively scan statements to find all variable declarations
    fn scan_and_declare_stmt(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let { name, ty, init, .. } => {
                if let Some(ty) = ty {
                    let vhdl_ty = self.type_to_vhdl(ty);
                    let default = self.default_value_for_type(ty);
                    self.writeln(&format!(
                        "variable {} : {} := {};",
                        name.name, vhdl_ty, default
                    ));
                    // Track struct types
                    if let crate::parser::TypeKind::Named(type_ident) = &ty.kind {
                        self.var_types
                            .insert(name.name.clone(), type_ident.name.clone());
                    }
                } else if let Some(init_expr) = init {
                    // Infer type from initializer
                    let width = self.infer_expr_width(init_expr);
                    self.writeln(&format!(
                        "variable {} : unsigned({} downto 0) := (others => '0');",
                        name.name,
                        width.saturating_sub(1)
                    ));
                } else {
                    // Fallback to 32-bit unsigned
                    self.writeln(&format!(
                        "variable {} : unsigned(31 downto 0) := (others => '0');",
                        name.name
                    ));
                }
            }
            StmtKind::If {
                then_block,
                else_block,
                ..
            } => {
                for s in &then_block.stmts {
                    self.scan_and_declare_stmt(s);
                }
                if let Some(eb) = else_block {
                    for s in &eb.stmts {
                        self.scan_and_declare_stmt(s);
                    }
                }
            }
            StmtKind::For { var, body, .. } => {
                // Loop variable declaration
                self.writeln(&format!("variable {} : integer := 0;", var.name));
                for s in &body.stmts {
                    self.scan_and_declare_stmt(s);
                }
            }
            StmtKind::While { body, .. } | StmtKind::Loop { body } => {
                for s in &body.stmts {
                    self.scan_and_declare_stmt(s);
                }
            }
            StmtKind::Block(block) => {
                for s in &block.stmts {
                    self.scan_and_declare_stmt(s);
                }
            }
            _ => {}
        }
    }

    /// Try to infer the bit width of an expression
    fn infer_expr_width(&self, expr: &Expr) -> u32 {
        match &expr.kind {
            ExprKind::Integer(n) => {
                if *n <= 255 {
                    8
                } else if *n <= 65535 {
                    16
                } else if *n <= 0xFFFF_FFFF {
                    32
                } else if *n <= 0xFFFF_FFFF_FFFF_FFFF {
                    64
                } else {
                    128
                }
            }
            ExprKind::Cast { ty, .. } => self.type_bit_width(ty),
            ExprKind::Binary { left, right, .. } => {
                let lw = self.infer_expr_width(left);
                let rw = self.infer_expr_width(right);
                lw.max(rw)
            }
            ExprKind::Paren(inner) => self.infer_expr_width(inner),
            ExprKind::Call { .. } | ExprKind::Ident(_) => 32,
            _ => 32,
        }
    }

    /// Check if a type is signed
    fn is_signed_type(&self, ty: &ParserType) -> bool {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => p.is_signed(),
            _ => false,
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
                // Variable is already declared in the declarative region.
                // Here we just handle the initialization assignment.
                if let Some(init) = init {
                    self.write_indent();
                    self.write(&format!("{} := ", name.name));
                    if let Some(ty) = ty {
                        self.generate_expr_with_width(init, self.type_bit_width(ty));
                    } else {
                        self.generate_expr(init);
                    }
                    self.write(";\n");
                }
            }
            StmtKind::Expr(expr) => {
                // Expression statements: only function/procedure calls make sense in VHDL
                match &expr.kind {
                    ExprKind::Call { .. }
                    | ExprKind::Builtin { .. }
                    | ExprKind::MethodCall { .. }
                    | ExprKind::TypeStaticCall { .. }
                    | ExprKind::GenericCall { .. } => {
                        self.write_indent();
                        self.generate_expr(expr);
                        self.write(";\n");
                    }
                    _ => {
                        self.writeln("-- expression statement (no side effect in VHDL)");
                    }
                }
            }
            StmtKind::Assign { target, value } => {
                self.write_indent();
                self.generate_expr(target);
                self.write(" := ");
                self.generate_expr(value);
                self.write(";\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                self.write_indent();
                self.generate_expr(target);
                self.write(" := ");
                // Expand compound assignment: target := target OP value
                self.generate_expr(target);
                self.write(" ");
                self.write(self.binary_op_to_vhdl(*op));
                self.write(" ");
                self.generate_expr(value);
                self.write(";\n");
            }
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.write_indent();
                self.write("if ");
                self.generate_condition(condition);
                self.write(" then\n");
                self.indent();
                self.generate_block(then_block);
                self.dedent();
                if let Some(else_block) = else_block {
                    self.writeln("else");
                    self.indent();
                    self.generate_block(else_block);
                    self.dedent();
                }
                self.writeln("end if;");
            }
            StmtKind::For {
                var,
                start,
                end,
                inclusive,
                body,
            } => {
                self.write_indent();
                self.write(&format!("for {} in ", var.name));
                self.generate_integer_expr(start);
                if *inclusive {
                    self.write(" to ");
                    self.generate_integer_expr(end);
                } else {
                    self.write(" to ");
                    self.generate_integer_expr(end);
                    self.write(" - 1");
                }
                self.write(" loop\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("end loop;");
            }
            StmtKind::While { condition, body } => {
                self.write_indent();
                self.write("while ");
                self.generate_condition(condition);
                self.write(" loop\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("end loop;");
            }
            StmtKind::Loop { body } => {
                self.writeln("loop");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("end loop;");
            }
            StmtKind::Break => {
                self.writeln("exit;");
            }
            StmtKind::Continue => {
                self.writeln("next;");
            }
            StmtKind::Return(expr) => {
                if let Some(expr) = expr {
                    self.write_indent();
                    self.write("v_result := ");
                    if let Some(w) = self.current_return_width {
                        self.generate_expr_with_width(expr, w);
                    } else {
                        self.generate_expr(expr);
                    }
                    self.write(";\n");
                    self.writeln("return v_result;");
                } else {
                    self.writeln("return;");
                }
            }
            StmtKind::Block(block) => {
                self.writeln("-- begin block");
                self.generate_block(block);
                self.writeln("-- end block");
            }
        }
    }

    /// Generate a condition expression (must produce boolean)
    fn generate_condition(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Bool(_)
            | ExprKind::Binary {
                op:
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
                    | BinaryOp::And
                    | BinaryOp::Or,
                ..
            }
            | ExprKind::Unary {
                op: UnaryOp::Not, ..
            } => {
                self.generate_expr(expr);
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.generate_condition(inner);
                self.write(")");
            }
            ExprKind::Ident(_) => {
                // Could be a boolean variable
                self.generate_expr(expr);
            }
            _ => {
                // Non-boolean expression used as condition: compare /= 0
                self.write("(");
                self.generate_expr(expr);
                self.write(") /= 0");
            }
        }
    }

    /// Generate an expression as an integer (for loop bounds, etc.)
    fn generate_integer_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                self.write(&format!("{}", n));
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.generate_integer_expr(inner);
                self.write(")");
            }
            ExprKind::Binary { left, op, right } => {
                self.generate_integer_expr(left);
                let op_str = match op {
                    BinaryOp::Add => " + ",
                    BinaryOp::Sub => " - ",
                    BinaryOp::Mul => " * ",
                    BinaryOp::Div => " / ",
                    BinaryOp::Rem => " mod ",
                    _ => " + ", // fallback
                };
                self.write(op_str);
                self.generate_integer_expr(right);
            }
            ExprKind::Cast { expr: inner, .. } => {
                self.write("to_integer(");
                self.generate_expr(inner);
                self.write(")");
            }
            _ => {
                self.write("to_integer(");
                self.generate_expr(expr);
                self.write(")");
            }
        }
    }

    /// Generate expression and resize to target width
    fn generate_expr_with_width(&mut self, expr: &Expr, target_width: u32) {
        // For integer literals, use to_unsigned directly
        if let ExprKind::Integer(n) = &expr.kind {
            self.write(&format!("to_unsigned({}, {})", n, target_width));
            return;
        }
        if let ExprKind::Bool(_) = &expr.kind {
            self.generate_expr(expr);
            return;
        }
        // For casts, generate directly
        if let ExprKind::Cast { .. } = &expr.kind {
            self.generate_expr(expr);
            return;
        }
        let inferred = self.infer_expr_width(expr);
        if inferred != target_width {
            self.write("resize(");
            self.generate_expr(expr);
            self.write(&format!(", {})", target_width));
        } else {
            self.generate_expr(expr);
        }
    }

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                // Default to 32-bit unsigned literals
                if *n <= 0xFFFF_FFFF {
                    self.write(&format!("to_unsigned({}, 32)", n));
                } else if *n <= 0xFFFF_FFFF_FFFF_FFFF {
                    self.write(&format!("to_unsigned({}, 64)", n));
                } else {
                    self.write(&format!("to_unsigned({}, 128)", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // Convert string to array of unsigned bytes
                self.generate_string_as_bytes(s);
            }
            ExprKind::Bytes(s) => {
                self.generate_string_as_bytes(s);
            }
            ExprKind::Hex(h) => {
                self.generate_hex_as_bytes(h);
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                self.generate_binary(left, *op, right);
            }
            ExprKind::Unary { op, operand } => match op {
                UnaryOp::Neg => {
                    self.write("(0 - ");
                    self.generate_expr(operand);
                    self.write(")");
                }
                UnaryOp::Not => {
                    self.write("not ");
                    self.generate_expr(operand);
                }
                UnaryOp::BitNot => {
                    self.write("not ");
                    self.generate_expr(operand);
                }
            },
            ExprKind::Index { array, index } => {
                self.generate_expr(array);
                self.write("(");
                self.generate_integer_expr(index);
                self.write(")");
            }
            ExprKind::Slice {
                array, start, end, ..
            } => {
                self.generate_expr(array);
                self.write("(");
                self.generate_integer_expr(start);
                self.write(" to ");
                self.generate_integer_expr(end);
                self.write(" - 1)");
            }
            ExprKind::Field { object, field } => {
                self.generate_expr(object);
                self.write(&format!(".{}", field.name));
            }
            ExprKind::Call { func, args } => {
                self.generate_call(func, args);
            }
            ExprKind::Builtin { name, args } => {
                self.generate_builtin(*name, args);
            }
            ExprKind::Array(elements) => {
                if elements.is_empty() {
                    self.write("(others => to_unsigned(0, 8))");
                } else {
                    self.write("(");
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
                self.write("(0 to ");
                self.generate_integer_expr(count);
                self.write(" - 1 => ");
                self.generate_expr(value);
                self.write(")");
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References are transparent in VHDL sequential code
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are transparent in VHDL sequential code
                self.generate_expr(inner);
            }
            ExprKind::Range { .. } => {
                self.write("/* range */");
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.generate_expr(inner);
                self.write(")");
            }
            ExprKind::StructLit { name: _, fields } => {
                self.write("(");
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("{} => ", field_name.name));
                    self.generate_expr(value);
                }
                self.write(")");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // VHDL doesn't have ternary; use a function-like idiom
                // For now, generate as if-else in a helper or use when/else at signal level
                // In sequential context, this is tricky. We use an IIFE-like pattern:
                self.generate_expr(then_expr);
                self.write(" when ");
                self.generate_condition(condition);
                self.write(" else ");
                self.generate_expr(else_expr);
            }
            ExprKind::EnumVariant {
                enum_name: _,
                variant_name,
                args,
            } => {
                if args.is_empty() {
                    self.write(&format!("ENUM_{}", variant_name.name.to_uppercase()));
                } else {
                    // Enum with data: construct a record
                    self.write(&format!("(tag => TAG_{}", variant_name.name.to_uppercase()));
                    for (i, arg) in args.iter().enumerate() {
                        self.write(&format!(
                            ", {}_v{} => ",
                            variant_name.name.to_lowercase(),
                            i
                        ));
                        self.generate_expr(arg);
                    }
                    self.write(", others => (others => '0'))");
                }
            }
            ExprKind::Match { expr, arms } => {
                // Generate match as a nested when/else chain
                // This is valid in VHDL concurrent context; for sequential, we generate
                // a case-when comment note
                self.write("-- match expression (simplified)\n");
                self.write_indent();
                // Use a case statement style
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write_indent();
                    }
                    self.generate_pattern_condition(&arm.pattern, expr);
                    self.write(" => ");
                    self.generate_expr(&arm.body);
                    if i < arms.len() - 1 {
                        self.write(",\n");
                    }
                }
            }
            ExprKind::MethodCall {
                receiver,
                mangled_name,
                args,
                ..
            } => {
                // Generate: func_mangled_name(receiver, args...)
                self.write(&format!("func_{}(", mangled_name));
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
                self.write(&format!("func_{}__{}", type_name.name, method_name.name));
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

    fn generate_binary(&mut self, left: &Expr, op: BinaryOp, right: &Expr) {
        match op {
            // Comparison ops produce boolean
            BinaryOp::Eq => {
                self.write("(");
                self.generate_expr(left);
                self.write(" = ");
                self.generate_expr(right);
                self.write(")");
            }
            BinaryOp::Ne => {
                self.write("(");
                self.generate_expr(left);
                self.write(" /= ");
                self.generate_expr(right);
                self.write(")");
            }
            BinaryOp::Lt => {
                self.write("(");
                self.generate_expr(left);
                self.write(" < ");
                self.generate_expr(right);
                self.write(")");
            }
            BinaryOp::Le => {
                self.write("(");
                self.generate_expr(left);
                self.write(" <= ");
                self.generate_expr(right);
                self.write(")");
            }
            BinaryOp::Gt => {
                self.write("(");
                self.generate_expr(left);
                self.write(" > ");
                self.generate_expr(right);
                self.write(")");
            }
            BinaryOp::Ge => {
                self.write("(");
                self.generate_expr(left);
                self.write(" >= ");
                self.generate_expr(right);
                self.write(")");
            }
            // Logical ops produce boolean
            BinaryOp::And => {
                self.write("(");
                self.generate_condition(left);
                self.write(" and ");
                self.generate_condition(right);
                self.write(")");
            }
            BinaryOp::Or => {
                self.write("(");
                self.generate_condition(left);
                self.write(" or ");
                self.generate_condition(right);
                self.write(")");
            }
            // Bitwise ops on unsigned
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
            // Shift ops
            BinaryOp::Shl => {
                self.write("shift_left(");
                self.generate_expr(left);
                self.write(", ");
                self.generate_shift_amount(right);
                self.write(")");
            }
            BinaryOp::Shr => {
                self.write("shift_right(");
                self.generate_expr(left);
                self.write(", ");
                self.generate_shift_amount(right);
                self.write(")");
            }
            // Arithmetic ops
            BinaryOp::Add => {
                self.write("(");
                self.generate_expr(left);
                self.write(" + ");
                self.generate_expr(right);
                self.write(")");
            }
            BinaryOp::Sub => {
                self.write("(");
                self.generate_expr(left);
                self.write(" - ");
                self.generate_expr(right);
                self.write(")");
            }
            BinaryOp::Mul => {
                // VHDL multiply doubles width; resize to keep original width
                self.write("resize(");
                self.generate_expr(left);
                self.write(" * ");
                self.generate_expr(right);
                let lw = self.infer_expr_width(left);
                self.write(&format!(", {})", lw));
            }
            BinaryOp::Div => {
                self.write("(");
                self.generate_expr(left);
                self.write(" / ");
                self.generate_expr(right);
                self.write(")");
            }
            BinaryOp::Rem => {
                self.write("(");
                self.generate_expr(left);
                self.write(" rem ");
                self.generate_expr(right);
                self.write(")");
            }
        }
    }

    /// Generate a shift amount as natural integer
    fn generate_shift_amount(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                self.write(&format!("{}", n));
            }
            _ => {
                self.write("to_integer(");
                self.generate_expr(expr);
                self.write(")");
            }
        }
    }

    /// Get the VHDL operator string for a binary op (used in compound assignment expansion)
    fn binary_op_to_vhdl(&self, op: BinaryOp) -> &'static str {
        match op {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::Div => "/",
            BinaryOp::Rem => "rem",
            BinaryOp::BitAnd => "and",
            BinaryOp::BitOr => "or",
            BinaryOp::BitXor => "xor",
            BinaryOp::Shl => "sll",
            BinaryOp::Shr => "srl",
            BinaryOp::Eq => "=",
            BinaryOp::Ne => "/=",
            BinaryOp::Lt => "<",
            BinaryOp::Le => "<=",
            BinaryOp::Gt => ">",
            BinaryOp::Ge => ">=",
            BinaryOp::And => "and",
            BinaryOp::Or => "or",
        }
    }

    fn generate_call(&mut self, func: &Expr, args: &[Expr]) {
        match &func.kind {
            ExprKind::Ident(ident) => {
                // Check for known function names
                let name = &ident.name;
                // Call as func_ prefixed
                self.write(&format!("func_{}", name));
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_expr(arg);
                }
                self.write(")");
            }
            ExprKind::Field { object, field } => {
                // Method call: object.method(args)
                if field.name == "len" && args.is_empty() {
                    // .len() -> 'length attribute
                    self.generate_expr(object);
                    self.write("'length");
                    return;
                }

                // Check for struct method calls
                if let ExprKind::Ident(obj_ident) = &object.kind
                    && let Some(struct_name) = self.var_types.get(&obj_ident.name).cloned()
                    && let Some(methods) = self.struct_methods.get(&struct_name).cloned()
                    && let Some(mangled_name) = methods.get(&field.name)
                {
                    self.write(&format!("func_{}(", mangled_name));
                    self.generate_expr(object);
                    for arg in args {
                        self.write(", ");
                        self.generate_expr(arg);
                    }
                    self.write(")");
                    return;
                }

                // General method call: generate as func_method(object, args)
                self.write(&format!("func_{}(", field.name));
                self.generate_expr(object);
                for arg in args {
                    self.write(", ");
                    self.generate_expr(arg);
                }
                self.write(")");
            }
            _ => {
                self.write("-- unsupported call target\n");
                self.write_indent();
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

    fn generate_builtin(&mut self, name: BuiltinFunc, args: &[Expr]) {
        match name {
            BuiltinFunc::Assert => {
                self.write("assert ");
                self.generate_condition(&args[0]);
                self.write(" report \"Assertion failed\" severity failure");
            }
        }
    }

    fn generate_cast(&mut self, inner: &Expr, ty: &ParserType) {
        use crate::parser::{PrimitiveType, TypeKind};

        match &ty.kind {
            TypeKind::Primitive(p) => {
                let bits = p.bit_width();
                let native = p.to_native();

                match native {
                    PrimitiveType::Bool => {
                        // Cast to bool: expr /= 0
                        self.write("(");
                        self.generate_expr(inner);
                        self.write(" /= 0)");
                    }
                    PrimitiveType::U8
                    | PrimitiveType::U16
                    | PrimitiveType::U32
                    | PrimitiveType::U64
                    | PrimitiveType::U128 => {
                        // Resize to target width
                        if let ExprKind::Integer(n) = &inner.kind {
                            self.write(&format!("to_unsigned({}, {})", n, bits));
                        } else {
                            self.write("resize(");
                            self.generate_expr(inner);
                            self.write(&format!(", {})", bits));
                        }
                    }
                    PrimitiveType::I8
                    | PrimitiveType::I16
                    | PrimitiveType::I32
                    | PrimitiveType::I64
                    | PrimitiveType::I128 => {
                        // Cast to signed
                        if let ExprKind::Integer(n) = &inner.kind {
                            self.write(&format!("to_signed({}, {})", n, bits));
                        } else {
                            self.write("resize(signed(");
                            self.generate_expr(inner);
                            self.write(&format!("), {})", bits));
                        }
                    }
                    _ => {
                        // Endian-qualified: just resize
                        if let ExprKind::Integer(n) = &inner.kind {
                            if p.is_signed() {
                                self.write(&format!("to_signed({}, {})", n, bits));
                            } else {
                                self.write(&format!("to_unsigned({}, {})", n, bits));
                            }
                        } else {
                            self.write("resize(");
                            self.generate_expr(inner);
                            self.write(&format!(", {})", bits));
                        }
                    }
                }
            }
            TypeKind::Array { element, size: _ } => {
                // Cast to array type - typically integer to byte array
                if let TypeKind::Primitive(PrimitiveType::U8) = &element.kind {
                    // Integer to byte array: generate as std_logic_vector conversion
                    self.write("-- cast to byte array\n");
                    self.write_indent();
                    self.generate_expr(inner);
                } else {
                    self.generate_expr(inner);
                }
            }
            TypeKind::Named(ident) => {
                // Cast to named type
                self.write(&format!("t_{}(", ident.name));
                self.generate_expr(inner);
                self.write(")");
            }
            _ => {
                // Fallback: just emit the expression
                self.generate_expr(inner);
            }
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    fn generate_pattern_condition(&mut self, pattern: &crate::parser::Pattern, scrutinee: &Expr) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("others");
            }
            PatternKind::Literal(lit_expr) => {
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(ident) => {
                self.write(&ident.name);
            }
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!("TAG_{}", variant_name.name.to_uppercase()));
            }
            PatternKind::Tuple(_) => {
                self.write("others -- tuple pattern");
            }
            PatternKind::Or(patterns) => {
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" | ");
                    }
                    self.generate_pattern_condition(p, scrutinee);
                }
            }
        }
    }

    /// Convert a string literal to a VHDL byte array aggregate
    fn generate_string_as_bytes(&mut self, s: &str) {
        let bytes: Vec<u8> = s.bytes().collect();
        if bytes.is_empty() {
            self.write("(others => to_unsigned(0, 8))");
            return;
        }
        self.write("(");
        for (i, b) in bytes.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&format!("to_unsigned({}, 8)", b));
        }
        self.write(")");
    }

    /// Convert a hex literal to a VHDL byte array aggregate
    fn generate_hex_as_bytes(&mut self, h: &str) {
        // Parse hex string into bytes
        let clean: String = h.chars().filter(|c| c.is_ascii_hexdigit()).collect();
        if clean.is_empty() {
            self.write("(others => to_unsigned(0, 8))");
            return;
        }
        self.write("(");
        let mut first = true;
        let mut i = 0;
        while i + 1 < clean.len() {
            if !first {
                self.write(", ");
            }
            first = false;
            let byte_str = &clean[i..i + 2];
            let val = u8::from_str_radix(byte_str, 16).unwrap_or(0);
            self.write(&format!("to_unsigned({}, 8)", val));
            i += 2;
        }
        // Handle odd trailing nibble
        if i < clean.len() {
            if !first {
                self.write(", ");
            }
            let byte_str = &clean[i..i + 1];
            let val = u8::from_str_radix(byte_str, 16).unwrap_or(0);
            self.write(&format!("to_unsigned({}, 8)", val));
        }
        self.write(")");
    }

    /// Collect all array type declarations needed
    fn collect_array_types(&self, ast: &Ast) -> Vec<String> {
        let mut types = Vec::new();
        let mut seen = std::collections::HashSet::new();

        for item in &ast.items {
            self.scan_item_for_array_types(item, &mut types, &mut seen);
        }
        types
    }

    fn scan_item_for_array_types(
        &self,
        item: &Item,
        types: &mut Vec<String>,
        seen: &mut std::collections::HashSet<String>,
    ) {
        match &item.kind {
            ItemKind::Function(func) => {
                self.scan_function_for_array_types(func, types, seen);
            }
            ItemKind::Const(c) => {
                self.scan_type_for_array_decl(&c.ty, types, seen);
            }
            ItemKind::Struct(s) => {
                for field in &s.fields {
                    self.scan_type_for_array_decl(&field.ty, types, seen);
                }
            }
            ItemKind::Layout(l) => {
                for field in &l.fields {
                    self.scan_type_for_array_decl(&field.ty, types, seen);
                }
            }
            ItemKind::Impl(impl_def) => {
                for method in &impl_def.methods {
                    self.scan_function_for_array_types(method, types, seen);
                }
            }
            ItemKind::Test(test) => {
                self.scan_block_for_array_types(&test.body, types, seen);
            }
            _ => {}
        }
    }

    fn scan_function_for_array_types(
        &self,
        func: &Function,
        types: &mut Vec<String>,
        seen: &mut std::collections::HashSet<String>,
    ) {
        for param in &func.params {
            self.scan_type_for_array_decl(&param.ty, types, seen);
        }
        if let Some(ret_ty) = &func.return_type {
            self.scan_type_for_array_decl(ret_ty, types, seen);
        }
        self.scan_block_for_array_types(&func.body, types, seen);
    }

    fn scan_block_for_array_types(
        &self,
        block: &Block,
        types: &mut Vec<String>,
        seen: &mut std::collections::HashSet<String>,
    ) {
        for stmt in &block.stmts {
            match &stmt.kind {
                StmtKind::Let { ty: Some(ty), .. } => {
                    self.scan_type_for_array_decl(ty, types, seen);
                }
                StmtKind::If {
                    then_block,
                    else_block,
                    ..
                } => {
                    self.scan_block_for_array_types(then_block, types, seen);
                    if let Some(eb) = else_block {
                        self.scan_block_for_array_types(eb, types, seen);
                    }
                }
                StmtKind::For { body, .. }
                | StmtKind::While { body, .. }
                | StmtKind::Loop { body } => {
                    self.scan_block_for_array_types(body, types, seen);
                }
                StmtKind::Block(block) => {
                    self.scan_block_for_array_types(block, types, seen);
                }
                _ => {}
            }
        }
    }

    fn scan_type_for_array_decl(
        &self,
        ty: &ParserType,
        types: &mut Vec<String>,
        seen: &mut std::collections::HashSet<String>,
    ) {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Array { element, size } => {
                let tag = self.type_to_tag(element);
                let elem_vhdl = self.element_type_vhdl(element);
                let type_name = format!("array_{}_{}", tag, size);
                if !seen.contains(&type_name) {
                    seen.insert(type_name.clone());
                    types.push(format!(
                        "type {} is array (0 to {}) of {};",
                        type_name,
                        size.saturating_sub(1),
                        elem_vhdl
                    ));
                }
                // Recurse for nested arrays
                self.scan_type_for_array_decl(element, types, seen);
            }
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                let tag = self.type_to_tag(element);
                let elem_vhdl = self.element_type_vhdl(element);
                let type_name = format!("array_{}_natural", tag);
                if !seen.contains(&type_name) {
                    seen.insert(type_name.clone());
                    types.push(format!(
                        "type {} is array (natural range <>) of {};",
                        type_name, elem_vhdl
                    ));
                }
                self.scan_type_for_array_decl(element, types, seen);
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                self.scan_type_for_array_decl(inner, types, seen);
            }
            _ => {}
        }
    }
}

impl Default for VhdlGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for VhdlGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();
        self.array_type_decls.clear();

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

        // Collect array types needed
        let array_types = self.collect_array_types(&ast.ast);

        // --- Emit VHDL ---

        self.writeln("-- Generated by AlgoC");
        self.writeln("-- DO NOT EDIT - This file is auto-generated");
        self.writeln("");
        self.writeln("library ieee;");
        self.writeln("use ieee.std_logic_1164.all;");
        self.writeln("use ieee.numeric_std.all;");
        self.writeln("");

        // Entity declaration
        self.writeln("entity testbench is");
        self.writeln("end entity testbench;");
        self.writeln("");

        // Architecture
        self.writeln("architecture behavior of testbench is");
        self.writeln("");
        self.indent();

        // Emit array type declarations
        for type_decl in &array_types {
            self.writeln(type_decl);
        }
        if !array_types.is_empty() {
            self.writeln("");
        }

        // Emit struct/record type declarations, enums, and constants
        for item in &ast.ast.items {
            match &item.kind {
                ItemKind::Struct(_) | ItemKind::Layout(_) | ItemKind::Enum(_) => {
                    self.generate_item(item);
                }
                ItemKind::Const(_) => {
                    self.generate_item(item);
                }
                _ => {}
            }
        }

        // Emit function/procedure declarations
        for item in &ast.ast.items {
            match &item.kind {
                ItemKind::Function(_) | ItemKind::Impl(_) => {
                    self.generate_item(item);
                }
                _ => {}
            }
        }

        // Emit test procedures
        if self.include_tests {
            for item in &ast.ast.items {
                if let ItemKind::Test(_) = &item.kind {
                    self.generate_item(item);
                }
            }
        }

        self.dedent();
        self.writeln("");
        self.writeln("begin");
        self.writeln("");
        self.indent();

        // Generate the test runner process
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

            self.writeln("-- Test runner process");
            self.writeln("test_runner : process");
            self.writeln("begin");
            self.indent();

            for name in &test_names {
                self.writeln(&format!("report \"Running test: {}\";", name));
                self.writeln(&format!("test_{}();", name));
                self.writeln(&format!("report \"PASS: {}\";", name));
                self.writeln("");
            }

            self.writeln("report \"All tests passed.\";");
            self.writeln("wait;");
            self.dedent();
            self.writeln("end process test_runner;");
        } else {
            // No tests: just a process that waits
            self.writeln("main : process");
            self.writeln("begin");
            self.indent();
            self.writeln("report \"AlgoC VHDL module loaded.\";");
            self.writeln("wait;");
            self.dedent();
            self.writeln("end process main;");
        }

        self.dedent();
        self.writeln("");
        self.writeln("end architecture behavior;");

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "vhd"
    }

    fn language_name(&self) -> &'static str {
        "VHDL"
    }
}
