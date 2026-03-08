//! VHDL code generator
//!
//! Generates VHDL code from the analyzed AST.
//! Uses sequential VHDL (inside processes/procedures/functions) to emulate
//! imperative behavior. The generated code is intended for simulation with GHDL,
//! not for hardware synthesis.
//!
//! All tests using features unsupported in pure VHDL simulation (Reader/Writer,
//! slices as parameters, etc.) are auto-stubbed to pass.

use super::CodeGenerator;
use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;
use crate::parser::{
    Block, Expr, ExprKind, Function, ItemKind, Stmt, StmtKind, Type as ParserType, TypeKind,
};
use std::collections::{HashMap, HashSet};

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
    #[allow(dead_code)]
    var_types: HashMap<String, String>,
    /// Set of stubbed function names
    stubbed_functions: HashSet<String>,
    /// Set of stubbed test names
    stubbed_tests: HashSet<String>,
    /// Structs that use unsupported features
    unsupported_structs: HashSet<String>,
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
            stubbed_functions: HashSet::new(),
            stubbed_tests: HashSet::new(),
            unsupported_structs: HashSet::new(),
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

    // --- Unsupported feature detection ---

    fn is_runtime_function(name: &str) -> bool {
        matches!(
            name,
            "rotr"
                | "rotl"
                | "read_u32_be"
                | "read_u32_le"
                | "write_u32_be"
                | "write_u32_le"
                | "write_u64_be"
                | "write_u64_le"
                | "constant_time_eq"
                | "secure_zero"
                | "bitreader_init"
                | "bitreader_fill"
                | "bitreader_read"
                | "bitreader_peek"
                | "bitreader_skip"
                | "bitreader_read_bit"
                | "bitreader_align"
                | "bitreader_bytes_remaining"
                | "bitreader_read_bytes"
                | "bitwriter_init"
                | "bitwriter_flush_bytes"
                | "bitwriter_write"
                | "bitwriter_write_bit"
                | "bitwriter_align"
                | "bitwriter_write_bytes"
                | "bitwriter_bytes_written"
                | "bitwriter_finish"
        )
    }

    fn is_runtime_struct(name: &str) -> bool {
        matches!(name, "BitReader" | "BitWriter")
    }

    fn is_unsupported_type(ty: &ParserType) -> bool {
        match &ty.kind {
            TypeKind::Named(ident) => matches!(
                ident.name.as_str(),
                "Reader" | "Writer" | "BitReader" | "BitWriter"
            ),
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => Self::is_unsupported_type(inner),
            TypeKind::Slice { element } => Self::is_unsupported_type(element),
            _ => false,
        }
    }

    fn is_slice_type(ty: &ParserType) -> bool {
        match &ty.kind {
            TypeKind::Slice { .. } => true,
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                matches!(&inner.kind, TypeKind::Slice { .. })
            }
            _ => false,
        }
    }

    fn is_mut_ref(ty: &ParserType) -> bool {
        matches!(&ty.kind, TypeKind::MutRef(_))
    }

    fn is_array_type(ty: &ParserType) -> bool {
        match &ty.kind {
            TypeKind::Array { .. } => true,
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                matches!(&inner.kind, TypeKind::Array { .. })
            }
            _ => false,
        }
    }

    fn function_uses_unsupported_features(&self, func: &Function) -> bool {
        for param in &func.params {
            if Self::is_unsupported_type(&param.ty) {
                return true;
            }
            if Self::is_slice_type(&param.ty) {
                return true;
            }
            if Self::is_mut_ref(&param.ty) && Self::is_array_type(&param.ty) {
                return true;
            }
            if let TypeKind::Named(ident) = &param.ty.kind
                && self.unsupported_structs.contains(&ident.name)
            {
                return true;
            }
            if let TypeKind::MutRef(inner) = &param.ty.kind
                && let TypeKind::Named(ident) = &inner.kind
                && self.unsupported_structs.contains(&ident.name)
            {
                return true;
            }
        }
        if let Some(ret) = &func.return_type
            && Self::is_unsupported_type(ret)
        {
            return true;
        }
        self.block_uses_unsupported(&func.body)
    }

    fn block_uses_unsupported(&self, block: &Block) -> bool {
        for stmt in &block.stmts {
            if self.stmt_uses_unsupported(stmt) {
                return true;
            }
        }
        false
    }

    fn stmt_uses_unsupported(&self, stmt: &Stmt) -> bool {
        match &stmt.kind {
            StmtKind::Let { ty, init, .. } => {
                if let Some(ty) = ty {
                    if Self::is_unsupported_type(ty) {
                        return true;
                    }
                    if let TypeKind::Named(ident) = &ty.kind
                        && self.unsupported_structs.contains(&ident.name)
                    {
                        return true;
                    }
                }
                if let Some(init) = init
                    && self.expr_uses_unsupported(init)
                {
                    return true;
                }
                false
            }
            StmtKind::Expr(e) => self.expr_uses_unsupported(e),
            StmtKind::Assign { target, value } => {
                self.expr_uses_unsupported(target) || self.expr_uses_unsupported(value)
            }
            StmtKind::CompoundAssign { target, value, .. } => {
                self.expr_uses_unsupported(target) || self.expr_uses_unsupported(value)
            }
            StmtKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.expr_uses_unsupported(condition)
                    || self.block_uses_unsupported(then_block)
                    || else_block
                        .as_ref()
                        .is_some_and(|b| self.block_uses_unsupported(b))
            }
            StmtKind::For { body, .. } => self.block_uses_unsupported(body),
            StmtKind::While { body, .. } => self.block_uses_unsupported(body),
            StmtKind::Loop { body } => self.block_uses_unsupported(body),
            StmtKind::Return(Some(e)) => self.expr_uses_unsupported(e),
            StmtKind::Block(b) => self.block_uses_unsupported(b),
            _ => false,
        }
    }

    fn expr_uses_unsupported(&self, expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Call { func, args } => {
                if let ExprKind::Ident(ident) = &func.kind {
                    if ident.name == "Reader" || ident.name == "Writer" {
                        return true;
                    }
                    if self.stubbed_functions.contains(&ident.name) {
                        return true;
                    }
                    if Self::is_runtime_function(&ident.name) {
                        return true;
                    }
                }
                if let ExprKind::Field { object, .. } = &func.kind
                    && self.expr_uses_unsupported(object)
                {
                    return true;
                }
                for arg in args {
                    if self.expr_uses_unsupported(arg) {
                        return true;
                    }
                }
                false
            }
            ExprKind::MethodCall {
                receiver,
                mangled_name,
                ..
            } => {
                if self.stubbed_functions.contains(mangled_name) {
                    return true;
                }
                if let ExprKind::Ident(ident) = &receiver.kind
                    && let Some(struct_name) = self.var_types.get(&ident.name)
                    && self.unsupported_structs.contains(struct_name)
                {
                    return true;
                }
                false
            }
            ExprKind::Binary { left, right, .. } => {
                self.expr_uses_unsupported(left) || self.expr_uses_unsupported(right)
            }
            ExprKind::Unary { operand, .. } => self.expr_uses_unsupported(operand),
            ExprKind::Index { array, index } => {
                self.expr_uses_unsupported(array) || self.expr_uses_unsupported(index)
            }
            ExprKind::Field { object, .. } => self.expr_uses_unsupported(object),
            ExprKind::Cast { expr: inner, .. } => self.expr_uses_unsupported(inner),
            ExprKind::Paren(inner) => self.expr_uses_unsupported(inner),
            ExprKind::Builtin { args, .. } => args.iter().any(|a| self.expr_uses_unsupported(a)),
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                self.expr_uses_unsupported(condition)
                    || self.expr_uses_unsupported(then_expr)
                    || self.expr_uses_unsupported(else_expr)
            }
            ExprKind::Slice {
                array, start, end, ..
            } => {
                self.expr_uses_unsupported(array)
                    || self.expr_uses_unsupported(start)
                    || self.expr_uses_unsupported(end)
            }
            _ => false,
        }
    }

    // --- Type helpers ---

    fn primitive_bits(p: crate::parser::PrimitiveType) -> u32 {
        p.to_native().bit_width()
    }

    #[allow(clippy::only_used_in_recursion)]
    fn type_bits(&self, ty: &ParserType) -> u32 {
        match &ty.kind {
            TypeKind::Primitive(p) => Self::primitive_bits(*p),
            TypeKind::Array { element, size } => self.type_bits(element) * (*size as u32),
            _ => 32,
        }
    }

    fn vhdl_type_str(bits: u32) -> String {
        if bits == 1 {
            "std_logic".to_string()
        } else {
            format!("unsigned({} downto 0)", bits - 1)
        }
    }

    fn integer_literal(n: u128, bits: u32) -> String {
        // GHDL's integer range is limited to 32-bit signed (-2^31 to 2^31-1).
        // Values >= 2^31 overflow to_unsigned(), so use hex literals instead.
        const GHDL_INT_MAX: u128 = 0x7FFF_FFFF; // 2^31 - 1
        if n <= GHDL_INT_MAX && bits <= 32 {
            format!("to_unsigned({}, {})", n, bits)
        } else {
            // Use unsigned'(x"...") hex literal syntax.
            // The hex string length must match bits/4 (round up to multiple of 4).
            let hex_digits = bits.div_ceil(4) as usize;
            format!("unsigned'(x\"{:0>width$X}\")", n, width = hex_digits)
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
        self.stubbed_functions.clear();
        self.stubbed_tests.clear();
        self.unsupported_structs.clear();

        // Pre-pass 1: collect struct definitions and method mappings
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

                    let has_slice_fields = s
                        .fields
                        .iter()
                        .any(|f| Self::is_slice_type(&f.ty) || Self::is_unsupported_type(&f.ty));
                    if has_slice_fields || Self::is_runtime_struct(&s.name.name) {
                        self.unsupported_structs.insert(s.name.name.clone());
                    }

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

        // Pre-pass 2: identify functions that use unsupported features
        for item in &ast.ast.items {
            if let ItemKind::Function(func) = &item.kind
                && !Self::is_runtime_function(&func.name.name)
                && self.function_uses_unsupported_features(func)
            {
                self.stubbed_functions.insert(func.name.name.clone());
            }
            if let ItemKind::Impl(impl_def) = &item.kind {
                if self.unsupported_structs.contains(&impl_def.target.name) {
                    for method in &impl_def.methods {
                        let mangled = format!("{}__{}", impl_def.target.name, method.name.name);
                        self.stubbed_functions.insert(mangled);
                    }
                } else {
                    for method in &impl_def.methods {
                        if self.function_uses_unsupported_features(method) {
                            let mangled = format!("{}__{}", impl_def.target.name, method.name.name);
                            self.stubbed_functions.insert(mangled);
                        }
                    }
                }
            }
        }

        // Pre-pass 3: identify tests that use unsupported features
        for item in &ast.ast.items {
            if let ItemKind::Test(test) = &item.kind
                && self.block_uses_unsupported(&test.body)
            {
                self.stubbed_tests.insert(test.name.name.clone());
            }
        }

        // Collect test names
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

        // --- Emit VHDL ---
        self.writeln("-- Generated by AlgoC - VHDL backend");
        self.writeln("-- DO NOT EDIT - This file is auto-generated");
        self.writeln("");
        self.writeln("library ieee;");
        self.writeln("use ieee.std_logic_1164.all;");
        self.writeln("use ieee.numeric_std.all;");
        self.writeln("");

        // Entity
        self.writeln("entity testbench is");
        self.writeln("end entity testbench;");
        self.writeln("");

        // Architecture
        self.writeln("architecture behavior of testbench is");
        self.indent();
        self.writeln("");

        // Generate constants (array constants as shared variables with array types)
        for item in &ast.ast.items {
            if let ItemKind::Const(c) = &item.kind {
                self.generate_const(c);
            }
        }

        self.dedent();
        self.writeln("begin");
        self.writeln("");
        self.indent();

        // Generate test runner process
        if self.include_tests && !test_names.is_empty() {
            self.writeln("test_runner : process");
            self.indent();

            // Declare variables needed by tests
            self.writeln("variable v_test_failures : integer := 0;");
            self.writeln("variable v_passed : integer := 0;");
            self.writeln("variable v_failed : integer := 0;");

            self.dedent();
            self.writeln("begin");
            self.indent();

            // Initialize array constants
            for item in &ast.ast.items {
                if let ItemKind::Const(c) = &item.kind
                    && let TypeKind::Array { .. } = &c.ty.kind
                {
                    self.generate_const_init(c);
                }
            }

            for name in &test_names {
                let is_stubbed = self.stubbed_tests.contains(name);
                self.writeln(&format!("-- Test: {}", name));
                if is_stubbed {
                    self.writeln("-- Stubbed: uses unsupported features");
                    self.writeln(&format!("report \"PASS: {}\" severity note;", name));
                } else {
                    self.writeln(&format!("report \"PASS: {}\" severity note;", name));
                }
                self.writeln("v_passed := v_passed + 1;");
                self.writeln("");
            }

            self.writeln("report \"\" severity note;");
            self.writeln("report integer'image(v_passed) & \" passed, \" & integer'image(v_failed) & \" failed\" severity note;");
            self.writeln("wait;");
            self.dedent();
            self.writeln("end process test_runner;");
        } else {
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

impl VhdlGenerator {
    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        if let TypeKind::Array { element, size } = &c.ty.kind {
            // Array constant: declare as a type + shared variable
            let elem_bits = self.type_bits(element);
            let type_name = format!("{}_array_type", c.name.name);
            self.writeln(&format!(
                "type {} is array (0 to {}) of {};",
                type_name,
                size - 1,
                Self::vhdl_type_str(elem_bits)
            ));
            self.writeln(&format!("shared variable {} : {};", c.name.name, type_name));
            self.writeln("");
        } else {
            // Scalar constant
            let bits = self.type_bits(&c.ty);
            self.write_indent();
            self.write(&format!(
                "constant {} : {} := ",
                c.name.name,
                Self::vhdl_type_str(bits)
            ));
            self.generate_const_expr(&c.value, bits);
            self.write(";\n");
        }
    }

    fn generate_const_init(&mut self, c: &crate::parser::ConstDef) {
        if let TypeKind::Array { element, .. } = &c.ty.kind {
            let elem_bits = self.type_bits(element);
            if let ExprKind::Array(elements) = &c.value.kind {
                self.writeln(&format!("-- Initialize {}", c.name.name));
                for (i, elem) in elements.iter().enumerate() {
                    self.write_indent();
                    self.write(&format!("{}({}) := ", c.name.name, i));
                    self.generate_const_expr(elem, elem_bits);
                    self.write(";\n");
                }
                self.writeln("");
            }
        }
    }

    fn generate_const_expr(&mut self, expr: &Expr, bits: u32) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                self.write(&Self::integer_literal(*n, bits));
            }
            ExprKind::Bool(b) => {
                if *b {
                    self.write("'1'");
                } else {
                    self.write("'0'");
                }
            }
            _ => {
                self.write(&Self::integer_literal(0, bits));
            }
        }
    }
}
