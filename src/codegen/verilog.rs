//! Verilog code generator
//!
//! Generates Verilog code from the analyzed AST.
//! Produces a self-contained testbench module compatible with iverilog/vvp.
//! Type mapping: u8->reg [7:0], u16->reg [15:0], u32->reg [31:0], u64->reg [63:0],
//!               u128->reg [127:0], bool->reg.
//! Functions become Verilog `function`, void functions become `task`.
//! Structs are flattened into separate variables with naming convention `structname_fieldname`.

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

/// Verilog code generator
pub struct VerilogGenerator {
    /// Current indentation level
    indent: usize,
    /// Output buffer
    output: String,
    /// Whether to include test functions and runner
    include_tests: bool,
    /// Struct definitions for flattened variable generation
    struct_defs: HashMap<String, Vec<StructFieldInfo>>,
    /// Struct methods: struct_name -> (method_name -> mangled_name)
    struct_methods: HashMap<String, MethodMap>,
    /// Variable types (for struct field access generation)
    var_types: HashMap<String, String>,
    /// Track integer variables that have been declared (to avoid re-declaring loop vars)
    declared_vars: Vec<HashMap<String, bool>>,
    /// Current function name (for return value assignment in Verilog functions)
    current_function_name: Option<String>,
}

impl VerilogGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
            include_tests: false,
            struct_defs: HashMap::new(),
            struct_methods: HashMap::new(),
            var_types: HashMap::new(),
            declared_vars: vec![HashMap::new()],
            current_function_name: None,
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

    fn push_scope(&mut self) {
        self.declared_vars.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.declared_vars.pop();
    }

    fn is_declared(&self, name: &str) -> bool {
        for scope in self.declared_vars.iter().rev() {
            if scope.contains_key(name) {
                return true;
            }
        }
        false
    }

    fn declare_var(&mut self, name: &str) {
        if let Some(scope) = self.declared_vars.last_mut() {
            scope.insert(name.to_string(), true);
        }
    }

    /// Convert a parser type to Verilog type declaration string
    fn type_to_verilog(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => self.primitive_to_verilog(*p),
            TypeKind::Array { element, size } => {
                let elem_type = self.type_to_verilog(element);
                format!("{} [0:{}]", elem_type, size - 1)
            }
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                // Slices/refs: treat as arrays with a reasonable default size
                let elem_type = self.type_to_verilog(element);
                format!("{} [0:255]", elem_type)
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.type_to_verilog(inner),
            TypeKind::Named(_) => {
                // Named types (structs) are flattened; use reg [31:0] as placeholder
                "reg [31:0]".to_string()
            }
            TypeKind::SelfType => "reg [31:0]".to_string(),
        }
    }

    /// Convert a primitive type to Verilog reg declaration
    fn primitive_to_verilog(&self, p: crate::parser::PrimitiveType) -> String {
        let native = p.to_native();
        let bits = native.bit_width();
        if bits == 1 {
            "reg".to_string()
        } else {
            format!("reg [{}:0]", bits - 1)
        }
    }

    /// Get the bit width of a type (for casts, etc.)
    fn type_bit_width(&self, ty: &ParserType) -> u32 {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => p.to_native().bit_width(),
            _ => 32,
        }
    }

    /// Generate parameter declaration for a function/task input
    fn param_to_verilog(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                let bits = native.bit_width();
                if bits == 1 {
                    "input".to_string()
                } else {
                    format!("input [{}:0]", bits - 1)
                }
            }
            TypeKind::Array { element, size } => {
                // Arrays as inputs aren't directly supported; flatten to wide input
                let elem_bits = self.type_bit_width(element);
                if elem_bits == 1 {
                    format!("input [0:{}]", size - 1)
                } else {
                    format!("input [{}:0]", (elem_bits as u64) * size - 1)
                }
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                // References become inout for mutable, input for immutable

                // Just treat as input for simplicity
                self.param_to_verilog(inner)
            }
            _ => "input [31:0]".to_string(),
        }
    }

    /// Get the return type width string for a function
    fn return_type_verilog(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                let bits = native.bit_width();
                if bits == 1 {
                    String::new()
                } else {
                    format!("[{}:0]", bits - 1)
                }
            }
            _ => "[31:0]".to_string(),
        }
    }

    /// Check if a function is void (no return type)
    fn is_void_function(func: &Function) -> bool {
        func.return_type.is_none()
    }

    fn generate_ast(&mut self, ast: &Ast) {
        for item in &ast.items {
            self.generate_item(item);
        }
    }

    /// Check if a function is a runtime library function that should be skipped.
    /// These functions use byte slices and other features that cannot be properly
    /// represented in Verilog.
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

    /// Check if a struct is a runtime library struct that should be skipped.
    fn is_runtime_struct(name: &str) -> bool {
        matches!(name, "BitReader" | "BitWriter")
    }

    fn generate_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => {
                if Self::is_runtime_function(&func.name.name) {
                    return;
                }
                self.generate_function(func);
            }
            ItemKind::Const(c) => self.generate_const(c),
            ItemKind::Struct(s) => {
                if Self::is_runtime_struct(&s.name.name) {
                    return;
                }
                self.generate_struct(s);
            }
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
                // Generate methods as standalone functions/tasks with mangled names
                for method in &impl_def.methods {
                    self.generate_method(&impl_def.target.name, method);
                }
            }
            ItemKind::Interface(_) => {
                // Interfaces are compile-time only, no runtime representation
            }
        }
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        self.write("localparam ");
        // Add type width for the parameter
        let bits = self.type_bit_width(&c.ty);
        if bits > 1 {
            self.write(&format!("[{}:0] ", bits - 1));
        }
        self.write(&format!("{} = ", c.name.name));
        self.generate_expr(&c.value);
        self.write(";\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Structs are flattened - emit a comment describing the struct
        self.writeln(&format!("// struct {} {{", s.name.name));
        for field in &s.fields {
            let vtype = self.type_to_verilog(&field.ty);
            self.writeln(&format!("//   {}: {}", field.name.name, vtype));
        }
        self.writeln("// }");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs - emit as comment
        self.writeln(&format!("// layout {} {{", l.name.name));
        for field in &l.fields {
            let vtype = self.type_to_verilog(&field.ty);
            self.writeln(&format!(
                "//   [{}:{}] {}: {}",
                field.bits_start, field.bits_end, field.name.name, vtype
            ));
        }
        self.writeln("// }");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum as localparam constants
        self.writeln(&format!("// enum {}", e.name.name));
        for (i, variant) in e.variants.iter().enumerate() {
            self.writeln(&format!(
                "localparam [31:0] {}_{} = 32'd{};",
                e.name.name, variant.name.name, i
            ));
        }
        self.writeln("");
    }

    fn generate_function(&mut self, func: &Function) {
        self.push_scope();

        if Self::is_void_function(func) {
            // Generate as task
            self.current_function_name = None;
            self.write_indent();
            self.write(&format!("task {};", func.name.name));
            self.write("\n");
            self.indent();

            // Declare inputs
            for param in &func.params {
                let vtype = self.param_to_verilog(&param.ty);
                self.writeln(&format!("{} {};", vtype, param.name.name));
                self.declare_var(&param.name.name);
            }

            // Generate local variable declarations from the body
            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endtask");
        } else {
            // Generate as function
            self.current_function_name = Some(func.name.name.clone());
            let ret_ty = func.return_type.as_ref().unwrap();
            let ret_width = self.return_type_verilog(ret_ty);
            self.write_indent();
            self.write(&format!("function {} {};", ret_width, func.name.name));
            self.write("\n");
            self.indent();

            // Declare inputs
            for param in &func.params {
                let vtype = self.param_to_verilog(&param.ty);
                self.writeln(&format!("{} {};", vtype, param.name.name));
                self.declare_var(&param.name.name);
            }

            // Generate local variable declarations from the body
            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endfunction");
        }
        self.current_function_name = None;
        self.writeln("");

        self.pop_scope();
    }

    fn generate_method(&mut self, struct_name: &str, func: &Function) {
        self.push_scope();

        let mangled_name = format!("{}__{}", struct_name, func.name.name);

        if Self::is_void_function(func) {
            self.current_function_name = None;
            self.write_indent();
            self.write(&format!("task {};", mangled_name));
            self.write("\n");
            self.indent();

            for param in &func.params {
                let vtype = self.param_to_verilog(&param.ty);
                self.writeln(&format!("{} {};", vtype, param.name.name));
                self.declare_var(&param.name.name);
            }

            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endtask");
        } else {
            self.current_function_name = Some(mangled_name.clone());
            let ret_ty = func.return_type.as_ref().unwrap();
            let ret_width = self.return_type_verilog(ret_ty);
            self.write_indent();
            self.write(&format!("function {} {};", ret_width, mangled_name));
            self.write("\n");
            self.indent();

            for param in &func.params {
                let vtype = self.param_to_verilog(&param.ty);
                self.writeln(&format!("{} {};", vtype, param.name.name));
                self.declare_var(&param.name.name);
            }

            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endfunction");
        }
        self.current_function_name = None;
        self.writeln("");

        self.pop_scope();
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.push_scope();

        // Tests are generated as tasks
        self.write_indent();
        self.write(&format!("task test_{};", test.name.name));
        self.write("\n");
        self.indent();

        self.generate_block_var_declarations(&test.body);

        self.writeln("begin");
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("end");

        self.dedent();
        self.writeln("endtask");
        self.writeln("");

        self.pop_scope();
    }

    /// Pre-scan a block to emit variable declarations at the beginning.
    /// In Verilog, variables must be declared before their procedural use inside
    /// function/task `begin..end` blocks (specifically for older Verilog standards).
    /// We scan the block for Let statements and emit `reg` declarations.
    fn generate_block_var_declarations(&mut self, block: &Block) {
        self.scan_block_vars(block);
    }

    /// Recursively scan a block for variable declarations and emit them
    fn scan_block_vars(&mut self, block: &Block) {
        for stmt in &block.stmts {
            self.scan_stmt_vars(stmt);
        }
    }

    /// Scan a statement for variable declarations
    fn scan_stmt_vars(&mut self, stmt: &Stmt) {
        match &stmt.kind {
            StmtKind::Let { name, ty, init, .. } => {
                if self.is_declared(&name.name) {
                    return;
                }
                self.declare_var(&name.name);
                let vtype = if let Some(ty) = ty {
                    self.type_to_verilog(ty)
                } else if let Some(init_expr) = init {
                    self.infer_verilog_type(init_expr)
                } else {
                    "reg [31:0]".to_string()
                };

                // Track struct types
                if let Some(ty) = ty
                    && let crate::parser::TypeKind::Named(type_ident) = &ty.kind
                {
                    self.var_types
                        .insert(name.name.clone(), type_ident.name.clone());
                }
                if let Some(init_expr) = init
                    && let ExprKind::Call { func, .. } = &init_expr.kind
                    && let ExprKind::Ident(func_ident) = &func.kind
                    && let Some(idx) = func_ident.name.find("__new")
                {
                    let sn = &func_ident.name[..idx];
                    self.var_types.insert(name.name.clone(), sn.to_string());
                }

                // Check for array types that need special declaration
                if let Some(ty) = ty {
                    if let crate::parser::TypeKind::Array { element, size } = &ty.kind {
                        let elem_vtype = self.type_to_verilog(element);
                        self.writeln(&format!("{} {} [0:{}];", elem_vtype, name.name, size - 1));
                        return;
                    }
                    // Check for named struct types - flatten to individual fields
                    if let crate::parser::TypeKind::Named(type_ident) = &ty.kind
                        && let Some(fields) = self.struct_defs.get(&type_ident.name).cloned()
                    {
                        for field in &fields {
                            let field_vtype = self.type_to_verilog(&field.ty);
                            self.writeln(&format!("{} {}_{};", field_vtype, name.name, field.name));
                        }
                        return;
                    }
                }

                self.writeln(&format!("{} {};", vtype, name.name));
            }
            StmtKind::For { var, body, .. } => {
                if !self.is_declared(&var.name) {
                    self.declare_var(&var.name);
                    self.writeln(&format!("integer {};", var.name));
                }
                self.scan_block_vars(body);
            }
            StmtKind::If {
                then_block,
                else_block,
                ..
            } => {
                self.scan_block_vars(then_block);
                if let Some(eb) = else_block {
                    self.scan_block_vars(eb);
                }
            }
            StmtKind::While { body, .. } => {
                self.scan_block_vars(body);
            }
            StmtKind::Loop { body } => {
                self.scan_block_vars(body);
            }
            StmtKind::Block(inner_block) => {
                self.scan_block_vars(inner_block);
            }
            _ => {}
        }
    }

    /// Infer a Verilog type from an expression
    fn infer_verilog_type(&self, expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Integer(n) => {
                if *n <= 0xFF {
                    "reg [7:0]".to_string()
                } else if *n <= 0xFFFF {
                    "reg [15:0]".to_string()
                } else if *n <= 0xFFFF_FFFF {
                    "reg [31:0]".to_string()
                } else if *n <= 0xFFFF_FFFF_FFFF_FFFF {
                    "reg [63:0]".to_string()
                } else {
                    "reg [127:0]".to_string()
                }
            }
            ExprKind::Bool(_) => "reg".to_string(),
            ExprKind::Cast { ty, .. } => self.type_to_verilog(ty),
            ExprKind::Binary { left, .. } => self.infer_verilog_type(left),
            ExprKind::Paren(inner) => self.infer_verilog_type(inner),
            ExprKind::Call { func, .. } => {
                // Try to look up function return type from name
                if let ExprKind::Ident(_ident) = &func.kind {
                    "reg [31:0]".to_string()
                } else {
                    "reg [31:0]".to_string()
                }
            }
            _ => "reg [31:0]".to_string(),
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
                // Variable was already declared in the pre-scan.
                // Just emit initialization if present.
                if let Some(init) = init {
                    // Check for struct literal initialization
                    if let ExprKind::StructLit {
                        name: struct_name,
                        fields,
                    } = &init.kind
                    {
                        let _ = struct_name;
                        for (field_ident, value) in fields {
                            self.write_indent();
                            self.write(&format!("{}_{} = ", name.name, field_ident.name));
                            self.generate_expr(value);
                            self.write(";\n");
                        }
                        return;
                    }
                    // Check for named struct type with factory call
                    if let Some(ty) = ty
                        && let crate::parser::TypeKind::Named(_) = &ty.kind
                    {
                        // If init is a function call that creates the struct, handle specially
                        if let ExprKind::Call { .. } = &init.kind {
                            // For struct types, generate the call but assign to flattened vars
                            self.write_indent();
                            self.write("// ");
                            self.write(&name.name);
                            self.write(" = ");
                            self.generate_expr(init);
                            self.write(";\n");
                            return;
                        }
                    }
                    self.write_indent();
                    self.write(&format!("{} = ", name.name));
                    self.generate_expr(init);
                    self.write(";\n");
                } else if let Some(ty) = ty {
                    // Initialize to default
                    let default_val = self.default_value_for_type(ty);
                    if !default_val.is_empty() {
                        // Check for named struct type - initialize flattened fields
                        if let crate::parser::TypeKind::Named(type_ident) = &ty.kind
                            && let Some(fields) = self.struct_defs.get(&type_ident.name).cloned()
                        {
                            for field in &fields {
                                let field_default = self.default_value_for_type(&field.ty);
                                self.writeln(&format!(
                                    "{}_{} = {};",
                                    name.name, field.name, field_default
                                ));
                            }
                            return;
                        }
                        self.writeln(&format!("{} = {};", name.name, default_val));
                    }
                }
            }
            StmtKind::Expr(expr) => {
                // Expression statements - in Verilog these are mainly task calls
                self.write_indent();
                self.generate_expr(expr);
                self.write(";\n");
            }
            StmtKind::Assign { target, value } => {
                // Check for struct field assignment
                if let ExprKind::Field { object, field } = &target.kind
                    && let ExprKind::Ident(obj_ident) = &object.kind
                    && self.var_types.contains_key(&obj_ident.name)
                {
                    self.write_indent();
                    self.write(&format!("{}_{} = ", obj_ident.name, field.name));
                    self.generate_expr(value);
                    self.write(";\n");
                    return;
                }
                self.write_indent();
                self.generate_expr(target);
                self.write(" = ");
                self.generate_expr(value);
                self.write(";\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                // Verilog doesn't have compound assignment operators.
                // Expand `a += b` to `a = a + b`
                self.write_indent();
                // Handle struct field compound assignment
                if let ExprKind::Field { object, field } = &target.kind
                    && let ExprKind::Ident(obj_ident) = &object.kind
                    && self.var_types.contains_key(&obj_ident.name)
                {
                    let var_name = format!("{}_{}", obj_ident.name, field.name);
                    self.write(&format!("{} = {} ", var_name, var_name));
                    self.write(self.binary_op_str(op));
                    self.write(" ");
                    self.generate_expr(value);
                    self.write(";\n");
                    return;
                }
                self.generate_expr(target);
                self.write(" = ");
                self.generate_expr(target);
                self.write(&format!(" {} ", self.binary_op_str(op)));
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
                self.write(") begin\n");
                self.indent();
                self.generate_block(then_block);
                self.dedent();
                if let Some(else_block) = else_block {
                    self.writeln("end else begin");
                    self.indent();
                    self.generate_block(else_block);
                    self.dedent();
                }
                self.writeln("end");
            }
            StmtKind::For {
                var,
                start,
                end,
                inclusive,
                body,
            } => {
                self.write_indent();
                self.write(&format!("for ({} = ", var.name));
                self.generate_expr(start);
                self.write(&format!(
                    "; {} {} ",
                    var.name,
                    if *inclusive { "<=" } else { "<" }
                ));
                self.generate_expr(end);
                self.write(&format!("; {} = {} + 1) begin\n", var.name, var.name));
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("end");
            }
            StmtKind::While { condition, body } => {
                self.write_indent();
                self.write("while (");
                self.generate_expr(condition);
                self.write(") begin\n");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("end");
            }
            StmtKind::Loop { body } => {
                self.writeln("while (1) begin");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("end");
            }
            StmtKind::Break => {
                self.writeln("disable _loop_block;");
            }
            StmtKind::Continue => {
                // Verilog doesn't have continue; use a comment placeholder
                self.writeln("// continue (not directly supported in Verilog)");
            }
            StmtKind::Return(expr) => {
                self.write_indent();
                if let Some(expr) = expr {
                    // In a Verilog function, return is done by assigning to the function name
                    let func_name = self
                        .current_function_name
                        .clone()
                        .unwrap_or_else(|| "__func_result".to_string());
                    self.write(&format!("{} = ", func_name));
                    self.generate_expr(expr);
                    self.write(";\n");
                } else {
                    self.write("// return void\n");
                }
            }
            StmtKind::Block(block) => {
                self.writeln("begin");
                self.indent();
                self.generate_block(block);
                self.dedent();
                self.writeln("end");
            }
        }
    }

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                // Use appropriate width literal
                if *n <= 0xFF {
                    self.write(&format!("{}", n));
                } else if *n <= 0xFFFF {
                    self.write(&format!("16'h{:X}", n));
                } else if *n <= 0xFFFF_FFFF {
                    self.write(&format!("32'h{:X}", n));
                } else if *n <= 0xFFFF_FFFF_FFFF_FFFF {
                    self.write(&format!("64'h{:X}", n));
                } else {
                    self.write(&format!("128'h{:X}", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "1'b1" } else { "1'b0" });
            }
            ExprKind::String(s) => {
                // Convert string to Verilog string (limited support)
                self.write(&format!("\"{}\"", escape_verilog_string(s)));
            }
            ExprKind::Bytes(s) => {
                // Convert bytes string to a hex representation
                let hex: String = s.as_bytes().iter().map(|b| format!("{:02x}", b)).collect();
                if hex.is_empty() {
                    self.write("8'h00");
                } else {
                    let bits = hex.len() * 4;
                    self.write(&format!("{}'h{}", bits, hex));
                }
            }
            ExprKind::Hex(h) => {
                if h.is_empty() {
                    self.write("8'h00");
                } else {
                    let bits = h.len() * 4;
                    self.write(&format!("{}'h{}", bits, h));
                }
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                self.write("(");
                self.generate_expr(left);
                let op_str = self.binary_op_str(op);
                self.write(&format!(" {} ", op_str));
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
                // Check for struct field via flattened naming
                if let ExprKind::Ident(ident) = &array.kind
                    && self.var_types.contains_key(&ident.name)
                {
                    // This might be struct[index] which isn't typical; just emit array index
                    self.write(&ident.name);
                    self.write("[");
                    self.generate_expr(index);
                    self.write("]");
                    return;
                }
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(index);
                self.write("]");
            }
            ExprKind::Slice {
                array,
                start,
                end,
                inclusive,
            } => {
                // Verilog part-select: arr[start +: width] or arr[high:low]
                // Use bit select notation
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(start);
                self.write(" +: (");
                self.generate_expr(end);
                self.write(" - ");
                self.generate_expr(start);
                if *inclusive {
                    self.write(" + 1");
                }
                self.write(")]");
            }
            ExprKind::Field { object, field } => {
                // Flatten struct field access: obj.field -> obj_field
                if let ExprKind::Ident(obj_ident) = &object.kind
                    && self.var_types.contains_key(&obj_ident.name)
                {
                    self.write(&format!("{}_{}", obj_ident.name, field.name));
                    return;
                }
                // For non-struct objects, fall back to underscore-joined naming
                self.generate_expr(object);
                self.write(&format!("_{}", field.name));
            }
            ExprKind::Call { func, args } => {
                // Check for method calls (object.method(args))
                if let ExprKind::Field { object, field } = &func.kind {
                    // len() -> size
                    if field.name == "len" && args.is_empty() {
                        // Verilog doesn't have a direct .len(); use $size or a constant
                        self.write("$size(");
                        self.generate_expr(object);
                        self.write(")");
                        return;
                    }

                    // Check for struct method calls
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

                    // Generic method call: generate as function call with object as first arg
                    self.generate_expr(object);
                    self.write(&format!("_{}(", field.name));
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(arg);
                    }
                    self.write(")");
                    return;
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
                    self.write("0");
                } else {
                    // Concatenation of elements: {e0, e1, e2, ...}
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
            ExprKind::ArrayRepeat { value, count } => {
                // Verilog repeat: {count{value}}
                self.write("{");
                self.generate_expr(count);
                self.write("{");
                self.generate_expr(value);
                self.write("}}");
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References are no-ops in Verilog
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are no-ops in Verilog
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
                // Struct literal - shouldn't normally appear in expression context
                // (handled specially in Let/Assign), but if it does, emit comment
                self.write(&format!("/* struct {} */", name.name));
                self.write("0");
                let _ = fields;
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // Verilog ternary
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
                // Emit enum constant
                self.write(&format!("{}_{}", enum_name.name, variant_name.name));
                if !args.is_empty() {
                    // Enum variants with data - simplified: just use the constant
                    self.write(" /* args: ");
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(arg);
                    }
                    self.write(" */");
                }
            }
            ExprKind::Match { expr, arms } => {
                // Use Verilog case expression (only valid in procedural context)
                // For expression context, use nested ternary
                self.generate_match_as_ternary(expr, arms);
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
                // Generate as mangled function call
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

    /// Generate a match expression as nested ternary operators
    fn generate_match_as_ternary(&mut self, expr: &Expr, arms: &[crate::parser::MatchArm]) {
        if arms.is_empty() {
            self.write("0");
            return;
        }
        for (i, arm) in arms.iter().enumerate() {
            let is_last = i == arms.len() - 1;
            let is_wildcard = matches!(arm.pattern.kind, crate::parser::PatternKind::Wildcard);

            if is_wildcard || is_last {
                // Default arm
                self.generate_expr(&arm.body);
                return;
            }

            self.write("(");
            self.generate_pattern_condition(&arm.pattern, expr);
            self.write(" ? ");
            self.generate_expr(&arm.body);
            self.write(" : ");
        }
        // Fallback
        self.write("0");
        // Close all parens
        for _ in 0..arms.len().saturating_sub(1) {
            self.write(")");
        }
    }

    /// Generate a pattern condition expression for ternary match
    fn generate_pattern_condition(&mut self, pattern: &crate::parser::Pattern, scrutinee: &Expr) {
        use crate::parser::PatternKind;
        match &pattern.kind {
            PatternKind::Wildcard => {
                self.write("1");
            }
            PatternKind::Literal(lit_expr) => {
                self.write("(");
                self.generate_expr(scrutinee);
                self.write(" == ");
                self.generate_expr(lit_expr);
                self.write(")");
            }
            PatternKind::Ident(_) => {
                // Binding pattern - always matches
                self.write("1");
            }
            PatternKind::EnumVariant {
                enum_name,
                variant_name,
                ..
            } => {
                self.write("(");
                self.generate_expr(scrutinee);
                self.write(&format!(" == {}_{}", enum_name.name, variant_name.name));
                self.write(")");
            }
            PatternKind::Tuple(_) => {
                self.write("1");
            }
            PatternKind::Or(patterns) => {
                self.write("(");
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" || ");
                    }
                    self.generate_pattern_condition(p, scrutinee);
                }
                self.write(")");
            }
        }
    }

    fn generate_builtin(&mut self, name: BuiltinFunc, args: &[Expr]) {
        match name {
            BuiltinFunc::Assert => {
                self.write("__assert(");
                if !args.is_empty() {
                    self.generate_expr(&args[0]);
                }
                self.write(")");
            }
        }
    }

    fn generate_cast(&mut self, expr: &Expr, ty: &ParserType) {
        use crate::parser::{PrimitiveType, TypeKind};

        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                let bits = native.bit_width();
                match native {
                    PrimitiveType::Bool => {
                        // Cast to bool: any non-zero is 1
                        self.write("(|");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    PrimitiveType::U8
                    | PrimitiveType::I8
                    | PrimitiveType::U16
                    | PrimitiveType::I16
                    | PrimitiveType::U32
                    | PrimitiveType::I32
                    | PrimitiveType::U64
                    | PrimitiveType::I64
                    | PrimitiveType::U128
                    | PrimitiveType::I128 => {
                        // Truncation via bit selection
                        self.write(&format!("({})'(", bits));
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    _ => {
                        // Endian-qualified types: just truncate to the right width
                        self.write(&format!("({})'(", bits));
                        self.generate_expr(expr);
                        self.write(")");
                    }
                }
            }
            TypeKind::Array { element, size } => {
                // Cast to array type - truncate or zero-extend
                let elem_bits = self.type_bit_width(element);
                let total_bits = elem_bits * (*size as u32);
                self.write(&format!("({})'(", total_bits));
                self.generate_expr(expr);
                self.write(")");
            }
            _ => {
                // For other types, pass through
                self.generate_expr(expr);
            }
        }
    }

    fn binary_op_str(&self, op: &BinaryOp) -> &'static str {
        match op {
            BinaryOp::Add => "+",
            BinaryOp::Sub => "-",
            BinaryOp::Mul => "*",
            BinaryOp::Div => "/",
            BinaryOp::Rem => "%",
            BinaryOp::BitAnd => "&",
            BinaryOp::BitOr => "|",
            BinaryOp::BitXor => "^",
            BinaryOp::Shl => "<<",
            BinaryOp::Shr => ">>",
            BinaryOp::Eq => "==",
            BinaryOp::Ne => "!=",
            BinaryOp::Lt => "<",
            BinaryOp::Le => "<=",
            BinaryOp::Gt => ">",
            BinaryOp::Ge => ">=",
            BinaryOp::And => "&&",
            BinaryOp::Or => "||",
        }
    }

    fn default_value_for_type(&self, ty: &ParserType) -> String {
        use crate::parser::TypeKind;
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let bits = p.to_native().bit_width();
                if bits == 1 {
                    "1'b0".to_string()
                } else {
                    "0".to_string()
                }
            }
            TypeKind::Array { .. } => {
                // Arrays: initialized element by element
                "0".to_string()
            }
            TypeKind::Named(_) => "0".to_string(),
            _ => "0".to_string(),
        }
    }
}

impl Default for VerilogGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for VerilogGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();
        self.var_types.clear();
        self.declared_vars = vec![HashMap::new()];
        self.current_function_name = None;

        // Pre-pass: collect struct definitions and method mappings
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

        self.writeln("// Generated by AlgoC - Verilog backend");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("`timescale 1ns / 1ps");
        self.writeln("");

        self.writeln("module testbench;");
        self.indent();
        self.writeln("");

        // Generate test failure tracking variables
        if self.include_tests {
            self.writeln("// Test tracking");
            self.writeln("integer __test_failures;");
            self.writeln("integer __passed;");
            self.writeln("integer __failed;");
            self.writeln("");

            // Generate assert task
            self.writeln("task __assert;");
            self.indent();
            self.writeln("input condition;");
            self.writeln("begin");
            self.indent();
            self.writeln("if (!condition) begin");
            self.indent();
            self.writeln("__test_failures = __test_failures + 1;");
            self.dedent();
            self.writeln("end");
            self.dedent();
            self.writeln("end");
            self.dedent();
            self.writeln("endtask");
            self.writeln("");
        }

        // Generate all items (functions, constants, structs, etc.)
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

        // Generate initial block for test runner
        if self.include_tests {
            self.writeln("// Test Runner");
            self.writeln("initial begin");
            self.indent();
            self.writeln("__passed = 0;");
            self.writeln("__failed = 0;");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("// Test: {}", name));
                self.writeln("__test_failures = 0;");
                self.writeln(&format!("test_{}();", name));
                self.writeln("if (__test_failures == 0) begin");
                self.indent();
                self.writeln(&format!("$display(\"PASS: {}\");", name));
                self.writeln("__passed = __passed + 1;");
                self.dedent();
                self.writeln("end else begin");
                self.indent();
                self.writeln(&format!("$display(\"FAIL: {}\");", name));
                self.writeln("__failed = __failed + 1;");
                self.dedent();
                self.writeln("end");
                self.writeln("");
            }

            self.writeln("$display(\"\");");
            self.writeln("$display(\"%0d passed, %0d failed\", __passed, __failed);");
            self.writeln("$finish;");
            self.dedent();
            self.writeln("end");
            self.writeln("");
        }

        self.dedent();
        self.writeln("endmodule");

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "v"
    }

    fn language_name(&self) -> &'static str {
        "Verilog"
    }
}

fn escape_verilog_string(s: &str) -> String {
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
