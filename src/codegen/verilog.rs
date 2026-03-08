//! Verilog code generator
//!
//! Generates Verilog-2001 code from the analyzed AST.
//! Produces a self-contained testbench module compatible with iverilog/vvp.
//! Type mapping: u8->reg [7:0], u16->reg [15:0], u32->reg [31:0], u64->reg [63:0],
//!               u128->reg [127:0], bool->reg.
//! Functions become Verilog `function`, void functions become `task`.
//! Structs are flattened into separate variables with naming convention `structname_fieldname`.
//!
//! Key Verilog-2001 constraints:
//! - No unpacked array parameters in functions/tasks
//! - No `$size()` (SystemVerilog only)
//! - No `(N)'(expr)` cast syntax (SystemVerilog only)
//! - No `localparam` arrays
//! - Array constants use `reg` memories initialized in `initial` block

use super::CodeGenerator;
use crate::analysis::AnalyzedAst;
use crate::errors::AlgocResult;
use crate::parser::{
    Ast, BinaryOp, Block, BuiltinFunc, Expr, ExprKind, Function, Item, ItemKind, Stmt, StmtKind,
    Type as ParserType, TypeKind, UnaryOp,
};
use std::collections::{HashMap, HashSet};

/// Struct field info for code generation
#[derive(Clone)]
struct StructFieldInfo {
    name: String,
    ty: ParserType,
}

/// Info about an array constant that needs initial block initialization
#[derive(Clone)]
struct ArrayConstInfo {
    name: String,
    #[allow(dead_code)]
    elem_bits: u32,
    #[allow(dead_code)]
    size: u64,
    values: Vec<String>,
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
    /// Track known array sizes for .len() calls
    array_sizes: HashMap<String, u64>,
    /// Array constants that need initialization in initial block
    array_consts: Vec<ArrayConstInfo>,
    /// Set of known task names (void functions) - need call syntax without assignment
    known_tasks: HashSet<String>,
    /// Current struct name (for resolving SelfType in methods)
    current_struct_name: Option<String>,
    /// Track which functions use unsupported features and should be stubbed
    stubbed_functions: HashSet<String>,
    /// Track which tests use unsupported features and should be auto-passed
    stubbed_tests: HashSet<String>,
    /// Structs that contain slice fields (can't be flattened for Verilog params)
    unsupported_structs: HashSet<String>,
    /// Functions that have been generated (to avoid duplicates)
    generated_functions: HashSet<String>,
    /// Track struct field array sizes: "structvar_field" -> size
    struct_field_array_sizes: HashMap<String, u64>,
    /// Functions that need slice params passed as packed vectors
    #[allow(dead_code)]
    func_param_info: HashMap<String, Vec<(String, bool)>>,
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
            array_sizes: HashMap::new(),
            array_consts: Vec::new(),
            known_tasks: HashSet::new(),
            current_struct_name: None,
            stubbed_functions: HashSet::new(),
            stubbed_tests: HashSet::new(),
            unsupported_structs: HashSet::new(),
            generated_functions: HashSet::new(),
            struct_field_array_sizes: HashMap::new(),
            func_param_info: HashMap::new(),
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

    // --- Type helpers ---

    /// Convert a parser type to Verilog reg declaration (for local variables)
    fn type_to_verilog(&self, ty: &ParserType) -> String {
        match &ty.kind {
            TypeKind::Primitive(p) => self.primitive_to_verilog(*p),
            TypeKind::Array { element, size } => {
                let elem_bits = self.type_bit_width(element);
                // For arrays, declare as: reg [elem_bits-1:0] name [0:size-1]
                // But we return just the element type; array dimensions are added separately
                if elem_bits == 1 {
                    format!("reg /*arr:{}*/", size)
                } else {
                    format!("reg [{}:0] /*arr:{}*/", elem_bits - 1, size)
                }
            }
            TypeKind::Slice { element } | TypeKind::ArrayRef { element, .. } => {
                // Slices: use packed byte vector approach
                let elem_bits = self.type_bit_width(element);
                if elem_bits == 1 {
                    "reg".to_string()
                } else {
                    format!("reg [{}:0]", elem_bits - 1)
                }
            }
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.type_to_verilog(inner),
            TypeKind::Named(ident) => {
                // Named types (structs) are flattened
                let _ = ident;
                "reg [31:0]".to_string()
            }
            TypeKind::SelfType => {
                // Resolve to current struct
                "reg [31:0]".to_string()
            }
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

    /// Get the bit width of a type
    #[allow(clippy::only_used_in_recursion)]
    fn type_bit_width(&self, ty: &ParserType) -> u32 {
        match &ty.kind {
            TypeKind::Primitive(p) => p.to_native().bit_width(),
            TypeKind::Array { element, size } => self.type_bit_width(element) * (*size as u32),
            _ => 32,
        }
    }

    /// Get bit width of element type for a parser type
    fn element_bit_width(&self, ty: &ParserType) -> u32 {
        match &ty.kind {
            TypeKind::Array { element, .. }
            | TypeKind::Slice { element }
            | TypeKind::ArrayRef { element, .. } => self.type_bit_width(element),
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => self.element_bit_width(inner),
            _ => 8,
        }
    }

    /// Check if a type is a slice or reference to slice
    fn is_slice_type(ty: &ParserType) -> bool {
        match &ty.kind {
            TypeKind::Slice { .. } => true,
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                matches!(&inner.kind, TypeKind::Slice { .. })
            }
            _ => false,
        }
    }

    /// Check if a type is an array
    fn is_array_type(ty: &ParserType) -> bool {
        match &ty.kind {
            TypeKind::Array { .. } => true,
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => {
                matches!(&inner.kind, TypeKind::Array { .. })
            }
            _ => false,
        }
    }

    /// Check if a type is a mutable reference
    fn is_mut_ref(ty: &ParserType) -> bool {
        matches!(&ty.kind, TypeKind::MutRef(_))
    }

    /// Get array size from type if it's a fixed-size array
    fn get_array_size(ty: &ParserType) -> Option<u64> {
        match &ty.kind {
            TypeKind::Array { size, .. } => Some(*size),
            TypeKind::ArrayRef { size, .. } => Some(*size),
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => Self::get_array_size(inner),
            _ => None,
        }
    }

    /// Check if a type uses Reader, Writer, or other unsupported features
    fn is_unsupported_type(ty: &ParserType) -> bool {
        match &ty.kind {
            TypeKind::Named(ident) => matches!(
                ident.name.as_str(),
                "Reader" | "Writer" | "BitReader" | "BitWriter"
            ),
            TypeKind::MutRef(inner) | TypeKind::Ref(inner) => Self::is_unsupported_type(inner),
            TypeKind::Slice { element } => {
                // Slices of unsupported types
                Self::is_unsupported_type(element)
            }
            _ => false,
        }
    }

    /// Check if a function uses unsupported features (Reader/Writer/slices/etc)
    fn function_uses_unsupported_features(&self, func: &Function) -> bool {
        // Check parameters
        for param in &func.params {
            if Self::is_unsupported_type(&param.ty) {
                return true;
            }
            // Slice parameters are unsupported in Verilog-2001 functions/tasks
            if Self::is_slice_type(&param.ty) {
                return true;
            }
            // Mutable array params (need inout unpacked arrays, not supported)
            if Self::is_mut_ref(&param.ty) && Self::is_array_type(&param.ty) {
                return true;
            }
            // Check for struct types with slice fields
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
            if let TypeKind::Ref(inner) = &param.ty.kind
                && let TypeKind::Named(ident) = &inner.kind
                && self.unsupported_structs.contains(&ident.name)
            {
                return true;
            }
        }
        // Check return type
        if let Some(ret) = &func.return_type
            && Self::is_unsupported_type(ret)
        {
            return true;
        }
        // Check body for calls to stubbed functions or use of unsupported types
        self.block_uses_unsupported(&func.body)
    }

    /// Check if a block uses unsupported features
    fn block_uses_unsupported(&self, block: &Block) -> bool {
        for stmt in &block.stmts {
            if self.stmt_uses_unsupported(stmt) {
                return true;
            }
        }
        false
    }

    /// Check if a statement uses unsupported features
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

    /// Check if an expression uses unsupported features
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
                    // Runtime functions that use slices
                    if Self::is_runtime_function(&ident.name) {
                        return true;
                    }
                }
                // Check for method calls on unsupported types
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
            ExprKind::MethodCall { receiver, .. } => {
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

    /// Check if a function is a runtime library function that should be skipped.
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

    // --- Code generation ---

    fn generate_ast(&mut self, ast: &Ast) {
        for item in &ast.items {
            self.generate_item(item);
        }
    }

    fn generate_item(&mut self, item: &Item) {
        match &item.kind {
            ItemKind::Function(func) => {
                if Self::is_runtime_function(&func.name.name) {
                    // Skip runtime functions - we inline them or stub them
                    return;
                }
                if self.stubbed_functions.contains(&func.name.name) {
                    return;
                }
                if self.generated_functions.contains(&func.name.name) {
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
                // Use statements are handled during loading
            }
            ItemKind::Impl(impl_def) => {
                if Self::is_runtime_struct(&impl_def.target.name) {
                    return;
                }
                if self.unsupported_structs.contains(&impl_def.target.name) {
                    return;
                }
                let struct_name = impl_def.target.name.clone();
                for method in &impl_def.methods {
                    let mangled = format!("{}__{}", struct_name, method.name.name);
                    if self.stubbed_functions.contains(&mangled) {
                        continue;
                    }
                    if self.generated_functions.contains(&mangled) {
                        continue;
                    }
                    self.current_struct_name = Some(struct_name.clone());
                    self.generate_method(&struct_name, method);
                    self.current_struct_name = None;
                }
            }
            ItemKind::Interface(_) => {
                // Interfaces are compile-time only
            }
        }
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        // Check if it's an array constant
        if let TypeKind::Array { element, size } = &c.ty.kind {
            let elem_bits = self.type_bit_width(element);
            // Collect array values
            let mut values = Vec::new();
            if let ExprKind::Array(elements) = &c.value.kind {
                for elem in elements {
                    values.push(self.expr_to_string(elem));
                }
            }

            // Track array size for .len() calls
            self.array_sizes.insert(c.name.name.clone(), *size);

            // Emit reg declaration for the array
            if elem_bits == 1 {
                self.writeln(&format!("reg {} [0:{}];", c.name.name, size - 1));
            } else {
                self.writeln(&format!(
                    "reg [{}:0] {} [0:{}];",
                    elem_bits - 1,
                    c.name.name,
                    size - 1
                ));
            }

            // Store for initial block initialization
            self.array_consts.push(ArrayConstInfo {
                name: c.name.name.clone(),
                elem_bits,
                size: *size,
                values,
            });
        } else {
            // Scalar constant
            let bits = self.type_bit_width(&c.ty);
            if bits > 1 {
                self.write_indent();
                self.write(&format!("localparam [{}:0] {} = ", bits - 1, c.name.name));
            } else {
                self.write_indent();
                self.write(&format!("localparam {} = ", c.name.name));
            }
            self.generate_expr(&c.value);
            self.write(";\n");
        }
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Structs are flattened - emit a comment describing the struct
        self.writeln(&format!("// struct {} {{", s.name.name));
        for field in &s.fields {
            self.writeln(&format!("//   {}: ...", field.name.name));
        }
        self.writeln("// }");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        self.writeln(&format!("// layout {} {{", l.name.name));
        for field in &l.fields {
            self.writeln(&format!(
                "//   [{}:{}] {}: ...",
                field.bits_start, field.bits_end, field.name.name
            ));
        }
        self.writeln("// }");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
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
        // Check if function uses unsupported features
        if self.function_uses_unsupported_features(func) {
            self.stubbed_functions.insert(func.name.name.clone());
            // Generate a stub
            self.generate_stub_function(func);
            self.generated_functions.insert(func.name.name.clone());
            return;
        }

        self.push_scope();
        self.generated_functions.insert(func.name.name.clone());

        // Check if this function has any slice/array parameters that make it
        // incompatible with Verilog-2001
        let has_slice_params = func.params.iter().any(|p| Self::is_slice_type(&p.ty));
        let has_mut_array_params = func
            .params
            .iter()
            .any(|p| Self::is_mut_ref(&p.ty) && Self::is_array_type(&p.ty));

        if has_slice_params || has_mut_array_params {
            // Functions with slice params or mutable array params
            // can't be represented as Verilog functions/tasks properly.
            // Generate as a task with packed wide vectors for slices.
            self.generate_packed_function(func);
            self.pop_scope();
            return;
        }

        if let Some(ret_ty) = func.return_type.as_ref() {
            // Generate as function
            self.current_function_name = Some(func.name.name.clone());
            let ret_width = self.return_type_width(ret_ty);
            self.write_indent();
            if ret_width.is_empty() {
                self.write(&format!("function {};\n", func.name.name));
            } else {
                self.write(&format!("function {} {};\n", ret_width, func.name.name));
            }
            self.indent();

            // Declare parameters
            let has_params = !func.params.is_empty();
            for param in &func.params {
                self.generate_param_decl(param, false);
            }

            // Verilog functions must have at least one input port
            if !has_params {
                self.writeln("input __dummy;");
                self.declare_var("__dummy");
            }

            // Pre-scan for local variable declarations
            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endfunction");
        } else {
            // Generate as task (no return type)
            self.current_function_name = None;
            self.write_indent();
            self.write(&format!("task {};\n", func.name.name));
            self.indent();

            for param in &func.params {
                self.generate_param_decl(param, false);
            }

            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endtask");
        }
        self.current_function_name = None;
        self.writeln("");

        self.pop_scope();
    }

    /// Generate a function with packed wide-vector parameters for slices
    #[allow(dead_code)]
    fn generate_packed_function(&mut self, func: &Function) {
        // For functions with slice params, we use packed byte vectors.
        // Each slice param `data: &[u8]` becomes:
        //   input [MAX_BYTES*8-1:0] data;
        //   input [31:0] data_len;
        // Byte i is accessed as: data[((data_len - 1 - i) * 8) +: 8]

        let is_void = func.return_type.is_none();

        if is_void {
            self.current_function_name = None;
            self.known_tasks.insert(func.name.name.clone());
            self.write_indent();
            self.write(&format!("task {};\n", func.name.name));
            self.indent();
        } else {
            self.current_function_name = Some(func.name.name.clone());
            let ret_ty = func.return_type.as_ref().unwrap();
            let ret_width = self.return_type_width(ret_ty);
            self.write_indent();
            if ret_width.is_empty() {
                self.write(&format!("function {};\n", func.name.name));
            } else {
                self.write(&format!("function {} {};\n", ret_width, func.name.name));
            }
            self.indent();
        }

        // Declare parameters
        for param in &func.params {
            if Self::is_slice_type(&param.ty) {
                // Packed byte vector: use a generous max size
                let elem_bits = self.element_bit_width(&param.ty);
                let max_bytes = 8192; // large enough for most uses
                let total_bits = max_bytes * elem_bits;
                let is_mut = Self::is_mut_ref(&param.ty);
                let dir = if is_mut { "inout" } else { "input" };
                self.writeln(&format!(
                    "{} [{}:0] {};",
                    dir,
                    total_bits - 1,
                    param.name.name
                ));
                self.writeln(&format!("input [31:0] {}_len;", param.name.name));
                self.declare_var(&param.name.name);
                let len_name = format!("{}_len", param.name.name);
                self.declare_var(&len_name);
                // Track as known array
                self.array_sizes
                    .insert(param.name.name.clone(), max_bytes as u64);
            } else if Self::is_mut_ref(&param.ty) && Self::is_array_type(&param.ty) {
                // Mutable array ref: pack as wide vector
                if let Some(size) = Self::get_array_size(&param.ty) {
                    let elem_bits = self.element_bit_width(&param.ty);
                    let total_bits = (size as u32) * elem_bits;
                    self.writeln(&format!(
                        "inout [{}:0] {};",
                        total_bits - 1,
                        param.name.name
                    ));
                    self.declare_var(&param.name.name);
                    self.array_sizes.insert(param.name.name.clone(), size);
                }
            } else {
                self.generate_param_decl(param, false);
            }
        }

        // Pre-scan for local variable declarations
        self.generate_block_var_declarations(&func.body);

        self.writeln("begin");
        self.indent();
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("end");

        self.dedent();
        if is_void {
            self.writeln("endtask");
        } else {
            self.writeln("endfunction");
        }
        self.current_function_name = None;
        self.writeln("");
    }

    /// Generate a stub for a function that uses unsupported features
    fn generate_stub_function(&mut self, func: &Function) {
        if let Some(ret_ty) = func.return_type.as_ref() {
            let ret_width = self.return_type_width(ret_ty);
            if ret_width.is_empty() {
                self.writeln(&format!("function {};", func.name.name));
            } else {
                self.writeln(&format!("function {} {};", ret_width, func.name.name));
            }
            self.indent();
            // Emit minimal params
            let has_params = !func.params.is_empty();
            for param in &func.params {
                let bits = self.type_bit_width(&param.ty);
                if bits > 1 {
                    self.writeln(&format!("input [{}:0] {};", bits - 1, param.name.name));
                } else {
                    self.writeln(&format!("input {};", param.name.name));
                }
            }
            // Verilog functions must have at least one input port
            if !has_params {
                self.writeln("input __dummy;");
            }
            self.writeln("begin");
            self.writeln(&format!("  {} = 0; // Stubbed", func.name.name));
            self.writeln("end");
            self.dedent();
            self.writeln("endfunction");
        } else {
            self.writeln(&format!("task {};", func.name.name));
            self.indent();
            self.writeln("begin");
            self.writeln("  // Stubbed: uses unsupported features");
            self.writeln("end");
            self.dedent();
            self.writeln("endtask");
        }
        self.writeln("");
    }

    /// Generate a parameter declaration for function/task
    fn generate_param_decl(&mut self, param: &crate::parser::Param, _is_inout: bool) {
        let ty = &param.ty;
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                let bits = native.bit_width();
                if bits == 1 {
                    self.writeln(&format!("input {};", param.name.name));
                } else {
                    self.writeln(&format!("input [{}:0] {};", bits - 1, param.name.name));
                }
            }
            TypeKind::Array { element, size } => {
                // Fixed-size array param: pack as wide vector
                let elem_bits = self.type_bit_width(element);
                let total_bits = (elem_bits as u64) * size;
                self.writeln(&format!(
                    "input [{}:0] {};",
                    total_bits - 1,
                    param.name.name
                ));
                self.array_sizes.insert(param.name.name.clone(), *size);
            }
            TypeKind::MutRef(inner) => {
                // Mutable ref: use inout
                // Resolve SelfType to current struct name
                let resolved_inner = if matches!(&inner.kind, TypeKind::SelfType) {
                    self.current_struct_name.clone()
                } else if let TypeKind::Named(ident) = &inner.kind {
                    Some(ident.name.clone())
                } else {
                    None
                };

                if let Some(struct_name) = resolved_inner {
                    // Struct ref: flatten fields
                    if let Some(fields) = self.struct_defs.get(&struct_name).cloned() {
                        for field in &fields {
                            let field_bits = self.type_bit_width(&field.ty);
                            let field_name = format!("{}_{}", param.name.name, field.name);
                            if Self::is_array_type(&field.ty) {
                                if let Some(sz) = Self::get_array_size(&field.ty) {
                                    self.writeln(&format!(
                                        "inout [{}:0] {};",
                                        field_bits - 1,
                                        field_name
                                    ));
                                    self.array_sizes.insert(field_name.clone(), sz);
                                    self.struct_field_array_sizes.insert(field_name.clone(), sz);
                                }
                            } else if field_bits == 1 {
                                self.writeln(&format!("inout {};", field_name));
                            } else {
                                self.writeln(&format!(
                                    "inout [{}:0] {};",
                                    field_bits - 1,
                                    field_name
                                ));
                            }
                        }
                        self.var_types
                            .insert(param.name.name.clone(), struct_name.clone());
                    } else {
                        self.writeln(&format!("inout [31:0] {};", param.name.name));
                    }
                } else {
                    match &inner.kind {
                        TypeKind::Primitive(p) => {
                            let bits = p.to_native().bit_width();
                            if bits == 1 {
                                self.writeln(&format!("inout {};", param.name.name));
                            } else {
                                self.writeln(&format!(
                                    "inout [{}:0] {};",
                                    bits - 1,
                                    param.name.name
                                ));
                            }
                        }
                        TypeKind::Array { element, size } => {
                            let elem_bits = self.type_bit_width(element);
                            let total_bits = (elem_bits as u64) * size;
                            self.writeln(&format!(
                                "inout [{}:0] {};",
                                total_bits - 1,
                                param.name.name
                            ));
                            self.array_sizes.insert(param.name.name.clone(), *size);
                        }
                        _ => {
                            self.writeln(&format!("inout [31:0] {};", param.name.name));
                        }
                    }
                }
            }
            TypeKind::Ref(inner) => {
                // Immutable ref
                // Resolve SelfType to current struct name
                let resolved_struct = if matches!(&inner.kind, TypeKind::SelfType) {
                    self.current_struct_name.clone()
                } else if let TypeKind::Named(ident) = &inner.kind {
                    Some(ident.name.clone())
                } else {
                    None
                };

                if let Some(struct_name) = resolved_struct {
                    // Struct ref: flatten fields as input
                    if let Some(fields) = self.struct_defs.get(&struct_name).cloned() {
                        for field in &fields {
                            let field_bits = self.type_bit_width(&field.ty);
                            let field_name = format!("{}_{}", param.name.name, field.name);
                            if Self::is_array_type(&field.ty) {
                                if let Some(sz) = Self::get_array_size(&field.ty) {
                                    self.writeln(&format!(
                                        "input [{}:0] {};",
                                        field_bits - 1,
                                        field_name
                                    ));
                                    self.array_sizes.insert(field_name.clone(), sz);
                                    self.struct_field_array_sizes.insert(field_name.clone(), sz);
                                }
                            } else if field_bits == 1 {
                                self.writeln(&format!("input {};", field_name));
                            } else {
                                self.writeln(&format!(
                                    "input [{}:0] {};",
                                    field_bits - 1,
                                    field_name
                                ));
                            }
                        }
                        self.var_types
                            .insert(param.name.name.clone(), struct_name.clone());
                    } else {
                        self.writeln(&format!("input [31:0] {};", param.name.name));
                    }
                } else {
                    match &inner.kind {
                        TypeKind::Array { element, size } => {
                            let elem_bits = self.type_bit_width(element);
                            let total_bits = (elem_bits as u64) * size;
                            self.writeln(&format!(
                                "input [{}:0] {};",
                                total_bits - 1,
                                param.name.name
                            ));
                            self.array_sizes.insert(param.name.name.clone(), *size);
                        }
                        _ => {
                            let bits = self.type_bit_width(inner);
                            if bits == 1 {
                                self.writeln(&format!("input {};", param.name.name));
                            } else {
                                self.writeln(&format!(
                                    "input [{}:0] {};",
                                    bits - 1,
                                    param.name.name
                                ));
                            }
                        }
                    }
                }
            }
            TypeKind::Named(ident) => {
                // Struct value param: flatten fields
                if let Some(fields) = self.struct_defs.get(&ident.name).cloned() {
                    for field in &fields {
                        let field_bits = self.type_bit_width(&field.ty);
                        let field_name = format!("{}_{}", param.name.name, field.name);
                        if Self::is_array_type(&field.ty) {
                            if let Some(sz) = Self::get_array_size(&field.ty) {
                                self.writeln(&format!(
                                    "input [{}:0] {};",
                                    field_bits - 1,
                                    field_name
                                ));
                                self.array_sizes.insert(field_name.clone(), sz);
                                self.struct_field_array_sizes.insert(field_name.clone(), sz);
                            }
                        } else if field_bits == 1 {
                            self.writeln(&format!("input {};", field_name));
                        } else {
                            self.writeln(&format!("input [{}:0] {};", field_bits - 1, field_name));
                        }
                    }
                    self.var_types
                        .insert(param.name.name.clone(), ident.name.clone());
                } else {
                    self.writeln(&format!("input [31:0] {};", param.name.name));
                }
            }
            TypeKind::SelfType => {
                // Bare SelfType: resolve to current struct and flatten as input
                if let Some(struct_name) = self.current_struct_name.clone() {
                    if let Some(fields) = self.struct_defs.get(&struct_name).cloned() {
                        for field in &fields {
                            let field_bits = self.type_bit_width(&field.ty);
                            let field_name = format!("{}_{}", param.name.name, field.name);
                            if Self::is_array_type(&field.ty) {
                                if let Some(sz) = Self::get_array_size(&field.ty) {
                                    self.writeln(&format!(
                                        "input [{}:0] {};",
                                        field_bits - 1,
                                        field_name
                                    ));
                                    self.array_sizes.insert(field_name.clone(), sz);
                                    self.struct_field_array_sizes.insert(field_name.clone(), sz);
                                }
                            } else if field_bits == 1 {
                                self.writeln(&format!("input {};", field_name));
                            } else {
                                self.writeln(&format!(
                                    "input [{}:0] {};",
                                    field_bits - 1,
                                    field_name
                                ));
                            }
                        }
                        self.var_types
                            .insert(param.name.name.clone(), struct_name.clone());
                    } else {
                        self.writeln(&format!("input [31:0] {};", param.name.name));
                    }
                } else {
                    self.writeln(&format!("input [31:0] {};", param.name.name));
                }
            }
            _ => {
                self.writeln(&format!("input [31:0] {};", param.name.name));
            }
        }
        self.declare_var(&param.name.name);
    }

    /// Get return type width string for a function
    fn return_type_width(&self, ty: &ParserType) -> String {
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

    /// Find the name of the local struct variable in a constructor body.
    /// Constructors typically have `let mut varname: StructType;` and then `return varname;`.
    fn find_constructor_local_var(&self, block: &Block, struct_name: &str) -> Option<String> {
        for stmt in &block.stmts {
            if let StmtKind::Let { name, ty, .. } = &stmt.kind
                && let Some(ty) = ty
                && let TypeKind::Named(ident) = &ty.kind
                && ident.name == struct_name
            {
                return Some(name.name.clone());
            }
        }
        None
    }

    /// Generate struct field declarations as inout parameters for a task.
    /// Used for constructors that return Self, where struct fields become inout params.
    fn generate_struct_inout_params(&mut self, param_prefix: &str, struct_name: &str) {
        if let Some(fields) = self.struct_defs.get(struct_name).cloned() {
            for field in &fields {
                let field_bits = self.type_bit_width(&field.ty);
                let field_name = format!("{}_{}", param_prefix, field.name);
                if Self::is_array_type(&field.ty) {
                    if let Some(sz) = Self::get_array_size(&field.ty) {
                        self.writeln(&format!("inout [{}:0] {};", field_bits - 1, field_name));
                        self.array_sizes.insert(field_name.clone(), sz);
                        self.struct_field_array_sizes.insert(field_name.clone(), sz);
                    }
                } else if field_bits == 1 {
                    self.writeln(&format!("inout {};", field_name));
                } else {
                    self.writeln(&format!("inout [{}:0] {};", field_bits - 1, field_name));
                }
                self.declare_var(&field_name);
            }
            self.var_types
                .insert(param_prefix.to_string(), struct_name.to_string());
            self.declare_var(param_prefix);
        }
    }

    fn generate_method(&mut self, struct_name: &str, func: &Function) {
        let mangled_name = format!("{}__{}", struct_name, func.name.name);

        // Check if method uses unsupported features
        if self.function_uses_unsupported_features(func) {
            self.stubbed_functions.insert(mangled_name.clone());
            // Generate stub
            if func.return_type.is_none() {
                self.writeln(&format!("// Stubbed task: {}", mangled_name));
            } else {
                self.writeln(&format!("// Stubbed function: {}", mangled_name));
            }
            self.writeln("");
            self.generated_functions.insert(mangled_name);
            return;
        }

        self.push_scope();
        self.generated_functions.insert(mangled_name.clone());
        self.current_struct_name = Some(struct_name.to_string());

        // Check if this is a static constructor returning Self
        let is_self_return = func.return_type.as_ref().is_some_and(|rt| {
            matches!(&rt.kind, TypeKind::SelfType)
                || matches!(&rt.kind, TypeKind::Named(ident) if ident.name == "Self")
        });
        let is_static_constructor = func.is_static && is_self_return;

        if is_static_constructor {
            // Static constructor returning Self -> generate as task with inout struct fields.
            // Find the local struct variable name used in the body (e.g., "state").
            let local_var_name = self
                .find_constructor_local_var(&func.body, struct_name)
                .unwrap_or_else(|| "self".to_string());

            self.current_function_name = None;
            self.known_tasks.insert(mangled_name.clone());
            self.write_indent();
            self.write(&format!("task {};\n", mangled_name));
            self.indent();

            // Generate the struct fields as inout parameters using the local var name as prefix
            self.generate_struct_inout_params(&local_var_name, struct_name);

            // Generate remaining params (beyond self, if any)
            for param in &func.params {
                self.generate_param_decl(param, false);
            }

            // Pre-scan for local variable declarations
            // The local struct variable is already declared as params, so scan_stmt_vars
            // will skip it because the fields are already declared.
            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endtask");
        } else if let Some(ret_ty) = func.return_type.as_ref() {
            // Generate as function
            self.current_function_name = Some(mangled_name.clone());

            let ret_width = self.return_type_width(ret_ty);

            self.write_indent();
            if ret_width.is_empty() {
                self.write(&format!("function {};\n", mangled_name));
            } else {
                self.write(&format!("function {} {};\n", ret_width, mangled_name));
            }
            self.indent();

            // Check if function has zero parameters - Verilog requires at least one input
            let has_params = !func.params.is_empty();

            for param in &func.params {
                self.generate_param_decl(param, false);
            }

            if !has_params {
                self.writeln("input __dummy;");
                self.declare_var("__dummy");
            }

            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endfunction");
        } else {
            // Generate as task (no return type)
            self.current_function_name = None;
            self.known_tasks.insert(mangled_name.clone());
            self.write_indent();
            self.write(&format!("task {};\n", mangled_name));
            self.indent();

            for param in &func.params {
                self.generate_param_decl(param, Self::is_mut_ref(&param.ty));
            }

            self.generate_block_var_declarations(&func.body);

            self.writeln("begin");
            self.indent();
            self.generate_block(&func.body);
            self.dedent();
            self.writeln("end");

            self.dedent();
            self.writeln("endtask");
        }
        self.current_function_name = None;
        self.current_struct_name = None;
        self.writeln("");

        self.pop_scope();
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        // Check if test uses unsupported features
        if self.block_uses_unsupported(&test.body) {
            self.stubbed_tests.insert(test.name.name.clone());
            // Generate empty task that auto-passes
            self.writeln(&format!(
                "task test_{}; // Stubbed: uses unsupported features",
                test.name.name
            ));
            self.indent();
            self.writeln("begin");
            self.writeln("  // Auto-pass: test uses features unsupported in Verilog");
            self.writeln("end");
            self.dedent();
            self.writeln("endtask");
            self.writeln("");
            return;
        }

        self.push_scope();

        // Tests are generated as tasks
        self.write_indent();
        self.write(&format!("task test_{};\n", test.name.name));
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

    /// Pre-scan a block to emit variable declarations at the beginning
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

                // Track struct types
                if let Some(ty) = ty
                    && let TypeKind::Named(type_ident) = &ty.kind
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

                // Check for array types
                if let Some(ty) = ty {
                    if let TypeKind::Array { element, size } = &ty.kind {
                        let elem_bits = self.type_bit_width(element);
                        self.array_sizes.insert(name.name.clone(), *size);
                        if elem_bits == 1 {
                            self.writeln(&format!("reg {} [0:{}];", name.name, size - 1));
                        } else {
                            self.writeln(&format!(
                                "reg [{}:0] {} [0:{}];",
                                elem_bits - 1,
                                name.name,
                                size - 1
                            ));
                        }
                        return;
                    }

                    // Check for named struct types - flatten to individual fields
                    if let TypeKind::Named(type_ident) = &ty.kind
                        && let Some(fields) = self.struct_defs.get(&type_ident.name).cloned()
                    {
                        for field in &fields {
                            let field_name = format!("{}_{}", name.name, field.name);
                            if let TypeKind::Array { element, size } = &field.ty.kind {
                                let eb = self.type_bit_width(element);
                                self.array_sizes.insert(field_name.clone(), *size);
                                self.struct_field_array_sizes
                                    .insert(field_name.clone(), *size);
                                if eb == 1 {
                                    self.writeln(&format!("reg {} [0:{}];", field_name, size - 1));
                                } else {
                                    self.writeln(&format!(
                                        "reg [{}:0] {} [0:{}];",
                                        eb - 1,
                                        field_name,
                                        size - 1
                                    ));
                                }
                            } else {
                                let field_vtype = self.type_to_verilog(&field.ty);
                                // Strip any array annotations from type_to_verilog
                                let clean_type = if let Some(pos) = field_vtype.find(" /*arr:") {
                                    field_vtype[..pos].to_string()
                                } else {
                                    field_vtype
                                };
                                self.writeln(&format!("{} {};", clean_type, field_name));
                            }
                        }
                        return;
                    }

                    // Slice types get a large packed reg + length
                    if Self::is_slice_type(ty) {
                        let elem_bits = self.element_bit_width(ty);
                        let max_bytes = 8192u32;
                        let total_bits = max_bytes * elem_bits;
                        self.writeln(&format!("reg [{}:0] {};", total_bits - 1, name.name));
                        let len_name = format!("{}_len", name.name);
                        self.writeln(&format!("reg [31:0] {};", len_name));
                        self.declare_var(&len_name);
                        return;
                    }
                }

                // Infer type from init expression
                let vtype = if let Some(ty) = ty {
                    let v = self.type_to_verilog(ty);
                    // Clean array annotations
                    if let Some(pos) = v.find(" /*arr:") {
                        v[..pos].to_string()
                    } else {
                        v
                    }
                } else if let Some(init_expr) = init {
                    self.infer_verilog_type(init_expr)
                } else {
                    "reg [31:0]".to_string()
                };

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
                if *n <= 0xFFFF_FFFF {
                    "reg [31:0]".to_string()
                } else if *n <= 0xFFFF_FFFF_FFFF_FFFF {
                    "reg [63:0]".to_string()
                } else {
                    "reg [127:0]".to_string()
                }
            }
            ExprKind::Bool(_) => "reg".to_string(),
            ExprKind::Cast { ty, .. } => {
                let v = self.type_to_verilog(ty);
                if let Some(pos) = v.find(" /*arr:") {
                    v[..pos].to_string()
                } else {
                    v
                }
            }
            ExprKind::Binary { left, .. } => self.infer_verilog_type(left),
            ExprKind::Paren(inner) => self.infer_verilog_type(inner),
            ExprKind::Call { func, .. } => {
                if let ExprKind::Ident(_ident) = &func.kind {
                    "reg [31:0]".to_string()
                } else {
                    "reg [31:0]".to_string()
                }
            }
            _ => "reg [31:0]".to_string(),
        }
    }

    // --- Statement generation ---

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
                    if let ExprKind::StructLit { fields, .. } = &init.kind {
                        for (field_ident, value) in fields {
                            self.write_indent();
                            self.write(&format!("{}_{} = ", name.name, field_ident.name));
                            self.generate_expr(value);
                            self.write(";\n");
                        }
                        return;
                    }

                    // Check for array literal initialization
                    if let ExprKind::Array(elements) = &init.kind {
                        for (i, elem) in elements.iter().enumerate() {
                            self.write_indent();
                            self.write(&format!("{}[{}] = ", name.name, i));
                            self.generate_expr(elem);
                            self.write(";\n");
                        }
                        return;
                    }

                    // Check for array repeat initialization
                    if let ExprKind::ArrayRepeat { value, count } = &init.kind {
                        // Generate a loop
                        if let ExprKind::Integer(n) = &count.kind {
                            for i in 0..*n {
                                self.write_indent();
                                self.write(&format!("{}[{}] = ", name.name, i));
                                self.generate_expr(value);
                                self.write(";\n");
                            }
                        }
                        return;
                    }

                    // Check for bytes/hex literals
                    if let ExprKind::Bytes(s) = &init.kind {
                        let bytes = s.as_bytes();
                        for (i, b) in bytes.iter().enumerate() {
                            self.writeln(&format!("{}[{}] = 8'h{:02x};", name.name, i, b));
                        }
                        // Track array size
                        self.array_sizes
                            .insert(name.name.clone(), bytes.len() as u64);
                        return;
                    }

                    if let ExprKind::Hex(h) = &init.kind {
                        let bytes_count = h.len() / 2;
                        for i in 0..bytes_count {
                            let hex_byte = &h[i * 2..i * 2 + 2];
                            self.writeln(&format!("{}[{}] = 8'h{};", name.name, i, hex_byte));
                        }
                        self.array_sizes
                            .insert(name.name.clone(), bytes_count as u64);
                        return;
                    }

                    // Named struct type with factory call (Call variant)
                    if let Some(ty) = ty
                        && let TypeKind::Named(type_ident) = &ty.kind
                        && let ExprKind::Call { func, .. } = &init.kind
                        && let ExprKind::Ident(func_ident) = &func.kind
                        && func_ident.name.contains("__new")
                    {
                        if self.known_tasks.contains(&func_ident.name) {
                            // Constructor is a task: call it with flattened struct fields
                            self.write_indent();
                            self.write(&format!("{}(", func_ident.name));
                            self.generate_struct_call_args_flat(&name.name, &type_ident.name, &[]);
                            self.write(");\n");
                        } else {
                            self.write_indent();
                            self.write("// struct init: ");
                            self.write(&name.name);
                            self.write("\n");
                        }
                        return;
                    }

                    // Named struct type with factory call (TypeStaticCall variant)
                    if let ExprKind::TypeStaticCall {
                        type_name,
                        method_name,
                        args: call_args,
                    } = &init.kind
                    {
                        let mangled = format!("{}__{}", type_name.name, method_name.name);
                        if self.known_tasks.contains(&mangled) {
                            // Constructor is a task: call it with flattened struct fields
                            self.write_indent();
                            self.write(&format!("{}(", mangled));
                            self.generate_struct_call_args_flat(
                                &name.name,
                                &type_name.name,
                                call_args,
                            );
                            self.write(");\n");
                        } else if self.stubbed_functions.contains(&mangled) {
                            // Stubbed constructor: just initialize to defaults
                            self.write_indent();
                            self.write("// struct init (stubbed): ");
                            self.write(&name.name);
                            self.write("\n");
                        } else {
                            // Function constructor: call it
                            self.write_indent();
                            self.write(&format!("{} = {}(", name.name, mangled));
                            for (i, arg) in call_args.iter().enumerate() {
                                if i > 0 {
                                    self.write(", ");
                                }
                                self.generate_expr(arg);
                            }
                            // Add dummy arg for zero-arg functions
                            if call_args.is_empty() {
                                self.write("0");
                            }
                            self.write(");\n");
                        }
                        return;
                    }

                    self.write_indent();
                    self.write(&format!("{} = ", name.name));
                    self.generate_expr(init);
                    self.write(";\n");
                } else if let Some(ty) = ty {
                    // Initialize to default
                    if let TypeKind::Named(type_ident) = &ty.kind
                        && let Some(fields) = self.struct_defs.get(&type_ident.name).cloned()
                    {
                        for field in &fields {
                            if Self::is_array_type(&field.ty) {
                                // Array fields: skip default init (already zero in simulation)
                            } else {
                                let default_val = self.default_value_for_type(&field.ty);
                                self.writeln(&format!(
                                    "{}_{} = {};",
                                    name.name, field.name, default_val
                                ));
                            }
                        }
                        return;
                    }
                    let default_val = self.default_value_for_type(ty);
                    if !default_val.is_empty() {
                        self.writeln(&format!("{} = {};", name.name, default_val));
                    }
                }
            }
            StmtKind::Expr(expr) => {
                self.write_indent();
                self.generate_expr(expr);
                self.write(";\n");
            }
            StmtKind::Assign { target, value } => {
                // Handle struct field assignment
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

                // Handle array index assignment on struct fields: state.block[i] = x
                if let ExprKind::Index { array, index } = &target.kind
                    && let ExprKind::Field { object, field } = &array.kind
                    && let ExprKind::Ident(obj_ident) = &object.kind
                    && self.var_types.contains_key(&obj_ident.name)
                {
                    self.write_indent();
                    self.write(&format!("{}_{}[", obj_ident.name, field.name));
                    self.generate_expr(index);
                    self.write("] = ");
                    self.generate_expr(value);
                    self.write(";\n");
                    return;
                }

                // Handle slice assignment: buf[offset..offset+4] as u32be = value
                if let ExprKind::Cast {
                    expr: slice_expr,
                    ty,
                } = &target.kind
                    && let ExprKind::Slice { array, start, .. } = &slice_expr.kind
                {
                    // This is a write to a byte buffer with endian conversion
                    self.generate_endian_write(array, start, ty, value);
                    return;
                }

                self.write_indent();
                self.generate_expr(target);
                self.write(" = ");
                self.generate_expr(value);
                self.write(";\n");
            }
            StmtKind::CompoundAssign { target, op, value } => {
                // Verilog doesn't have compound assignment operators
                self.write_indent();
                // Handle struct field compound assignment
                if let ExprKind::Field { object, field } = &target.kind
                    && let ExprKind::Ident(obj_ident) = &object.kind
                    && self.var_types.contains_key(&obj_ident.name)
                {
                    let var_name = format!("{}_{}", obj_ident.name, field.name);
                    self.write(&format!(
                        "{} = {} {} ",
                        var_name,
                        var_name,
                        self.binary_op_str(op)
                    ));
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
                self.writeln("// continue (not directly supported in Verilog)");
            }
            StmtKind::Return(expr) => {
                self.write_indent();
                if let Some(expr) = expr {
                    if let Some(func_name) = self.current_function_name.clone() {
                        // In a function: assign to function name (Verilog return convention)
                        self.write(&format!("{} = ", func_name));
                        self.generate_expr(expr);
                        self.write(";\n");
                    } else if let ExprKind::Ident(ident) = &expr.kind
                        && self.var_types.contains_key(&ident.name)
                    {
                        // In a task returning a struct variable (constructor-as-task):
                        // the struct fields are already written via inout params, so no-op
                        self.write("// return via inout params\n");
                    } else {
                        self.write("// return (task)\n");
                    }
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

    /// Generate endian write: buf[offset..offset+N] as u32be = value
    fn generate_endian_write(&mut self, array: &Expr, start: &Expr, ty: &ParserType, value: &Expr) {
        use crate::parser::PrimitiveType;
        if let TypeKind::Primitive(p) = &ty.kind {
            let native = p.to_native();
            let bits = native.bit_width();
            let is_be = matches!(
                p,
                PrimitiveType::U16Be
                    | PrimitiveType::U32Be
                    | PrimitiveType::U64Be
                    | PrimitiveType::U128Be
                    | PrimitiveType::I16Be
                    | PrimitiveType::I32Be
                    | PrimitiveType::I64Be
                    | PrimitiveType::I128Be
            );
            let num_bytes = bits / 8;
            // Generate byte-by-byte write
            for i in 0..num_bytes {
                self.write_indent();
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(start);
                if i > 0 {
                    self.write(&format!(" + {}", i));
                }
                self.write("] = ");
                // Extract byte from value
                let shift_amount = if is_be {
                    (num_bytes - 1 - i) * 8
                } else {
                    i * 8
                };
                if shift_amount > 0 {
                    self.write("(");
                    self.generate_expr(value);
                    self.write(&format!(") >> {}", shift_amount));
                } else {
                    self.generate_expr(value);
                }
                self.write(";\n");
            }
        }
    }

    // --- Expression generation ---

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                if *n == 0 {
                    self.write("0");
                } else if *n <= 0xFFFF_FFFF {
                    self.write(&format!("32'h{:08X}", n));
                } else if *n <= 0xFFFF_FFFF_FFFF_FFFF {
                    self.write(&format!("64'h{:016X}", n));
                } else {
                    self.write(&format!("128'h{:032X}", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "1'b1" } else { "1'b0" });
            }
            ExprKind::String(s) => {
                self.write(&format!("\"{}\"", escape_verilog_string(s)));
            }
            ExprKind::Bytes(s) => {
                // Bytes literals need to become a series of byte assignments
                // In expression context, create a wide packed value
                let bytes = s.as_bytes();
                if bytes.is_empty() {
                    self.write("8'h00");
                } else {
                    // Pack bytes MSB-first for array indexing
                    let hex: String = bytes.iter().map(|b| format!("{:02x}", b)).collect();
                    let bits = bytes.len() * 8;
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
                // Handle struct field array indexing: state.field[i]
                if let ExprKind::Field { object, field } = &array.kind
                    && let ExprKind::Ident(obj_ident) = &object.kind
                    && self.var_types.contains_key(&obj_ident.name)
                {
                    self.write(&format!("{}_{}[", obj_ident.name, field.name));
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
                // Slicing with endian conversion is handled specially in Cast
                // For plain slicing, use Verilog part-select
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
                // For non-struct objects, use underscore-joined naming
                self.generate_expr(object);
                self.write(&format!("_{}", field.name));
            }
            ExprKind::Call { func, args } => {
                self.generate_call(func, args);
            }
            ExprKind::Builtin { name, args } => {
                self.generate_builtin(*name, args);
            }
            ExprKind::Array(elements) => {
                if elements.is_empty() {
                    self.write("0");
                } else {
                    // Concatenation: {e0, e1, e2, ...}
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
            ExprKind::StructLit { name, fields } => {
                // Struct literal in expression context - emit 0
                self.write(&format!("/* struct {} */ 0", name.name));
                let _ = fields;
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
                ..
            } => {
                self.write(&format!("{}_{}", enum_name.name, variant_name.name));
            }
            ExprKind::Match { expr, arms } => {
                self.generate_match_as_ternary(expr, arms);
            }
            ExprKind::MethodCall {
                receiver,
                method_name,
                mangled_name,
                args,
            } => {
                // Check if it's a .len() call
                if method_name == "len" && args.is_empty() {
                    self.generate_len_expr(receiver);
                    return;
                }

                // Check if the mangled name is a known task
                if self.known_tasks.contains(mangled_name) {
                    // Task call: in statement context, no return
                    self.write(&format!("{}(", mangled_name));
                    self.generate_method_call_args(receiver, args);
                    self.write(")");
                } else {
                    self.write(&format!("{}(", mangled_name));
                    self.generate_method_call_args(receiver, args);
                    self.write(")");
                }
            }
            ExprKind::TypeStaticCall {
                type_name,
                method_name,
                args,
            } => {
                let mangled = format!("{}__{}", type_name.name, method_name.name);
                if self.stubbed_functions.contains(&mangled) {
                    // Stubbed: just emit 0
                    self.write("0 /* stubbed */");
                } else {
                    self.write(&format!("{}(", mangled));
                    if args.is_empty() && !self.known_tasks.contains(&mangled) {
                        // Zero-arg function: pass dummy argument
                        self.write("0");
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
            ExprKind::GenericCall { func, args, .. } => {
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

    /// Generate a function/task call
    fn generate_call(&mut self, func: &Expr, args: &[Expr]) {
        // Check for method calls via Field: object.method(args)
        if let ExprKind::Field { object, field } = &func.kind {
            // .len() call
            if field.name == "len" && args.is_empty() {
                self.generate_len_expr(object);
                return;
            }

            // Struct method calls
            if let ExprKind::Ident(obj_ident) = &object.kind
                && let Some(struct_name) = self.var_types.get(&obj_ident.name).cloned()
                && let Some(methods) = self.struct_methods.get(&struct_name).cloned()
                && let Some(mangled_name) = methods.get(&field.name)
            {
                self.write(&format!("{}(", mangled_name));
                // Pass struct fields as args
                self.generate_struct_call_args(&obj_ident.name, &struct_name, args);
                self.write(")");
                return;
            }

            // Generic method call
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

        // Regular function call
        if let ExprKind::Ident(ident) = &func.kind {
            // Check for runtime function inlining
            if ident.name == "rotr" && args.len() == 2 {
                // rotr(x, n) = (x >> n) | (x << (32 - n))
                self.write("((");
                self.generate_expr(&args[0]);
                self.write(" >> ");
                self.generate_expr(&args[1]);
                self.write(") | (");
                self.generate_expr(&args[0]);
                self.write(" << (32 - ");
                self.generate_expr(&args[1]);
                self.write(")))");
                return;
            }
            if ident.name == "rotl" && args.len() == 2 {
                // rotl(x, n) = (x << n) | (x >> (32 - n))
                self.write("((");
                self.generate_expr(&args[0]);
                self.write(" << ");
                self.generate_expr(&args[1]);
                self.write(") | (");
                self.generate_expr(&args[0]);
                self.write(" >> (32 - ");
                self.generate_expr(&args[1]);
                self.write(")))");
                return;
            }
        }

        self.generate_expr(func);
        self.write("(");
        let mut first = true;
        for arg in args.iter() {
            // Check if this argument is a struct variable that needs flattening
            if let ExprKind::Ident(ident) = &arg.kind
                && let Some(struct_name) = self.var_types.get(&ident.name).cloned()
                && let Some(fields) = self.struct_defs.get(&struct_name).cloned()
            {
                for field in &fields {
                    if !first {
                        self.write(", ");
                    }
                    first = false;
                    self.write(&format!("{}_{}", ident.name, field.name));
                }
                continue;
            }
            // Also handle &var and &mut var wrapping a struct variable
            if let ExprKind::Ref(inner) | ExprKind::MutRef(inner) = &arg.kind
                && let ExprKind::Ident(ident) = &inner.kind
                && let Some(struct_name) = self.var_types.get(&ident.name).cloned()
                && let Some(fields) = self.struct_defs.get(&struct_name).cloned()
            {
                for field in &fields {
                    if !first {
                        self.write(", ");
                    }
                    first = false;
                    self.write(&format!("{}_{}", ident.name, field.name));
                }
                continue;
            }
            if !first {
                self.write(", ");
            }
            first = false;
            self.generate_expr(arg);
        }
        self.write(")");
    }

    /// Generate args for a method call, including the receiver (struct fields)
    fn generate_method_call_args(&mut self, receiver: &Expr, args: &[Expr]) {
        // If receiver is a struct variable, pass its flattened fields
        if let ExprKind::Ident(obj_ident) = &receiver.kind
            && let Some(struct_name) = self.var_types.get(&obj_ident.name).cloned()
        {
            self.generate_struct_call_args(&obj_ident.name, &struct_name, args);
            return;
        }
        // Fallback: pass receiver as-is
        self.generate_expr(receiver);
        for arg in args {
            self.write(", ");
            self.generate_expr(arg);
        }
    }

    /// Generate arguments for calling a function that takes struct fields
    fn generate_struct_call_args(
        &mut self,
        var_name: &str,
        struct_name: &str,
        extra_args: &[Expr],
    ) {
        if let Some(fields) = self.struct_defs.get(struct_name).cloned() {
            for (i, field) in fields.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(&format!("{}_{}", var_name, field.name));
            }
            for arg in extra_args {
                self.write(", ");
                self.generate_expr(arg);
            }
        } else {
            self.write(var_name);
            for arg in extra_args {
                self.write(", ");
                self.generate_expr(arg);
            }
        }
    }

    /// Generate arguments for calling a task/function that takes struct fields,
    /// with additional expression args.
    fn generate_struct_call_args_flat(
        &mut self,
        var_name: &str,
        struct_name: &str,
        extra_args: &[Expr],
    ) {
        self.generate_struct_call_args(var_name, struct_name, extra_args);
    }

    /// Generate .len() expression
    fn generate_len_expr(&mut self, object: &Expr) {
        // Try to find the known size
        if let ExprKind::Ident(ident) = &object.kind {
            // Check for _len companion variable (for slice params)
            let len_name = format!("{}_len", ident.name);
            if self.is_declared(&len_name) {
                self.write(&len_name);
                return;
            }
            // Check for known array size
            if let Some(size) = self.array_sizes.get(&ident.name) {
                self.write(&format!("{}", size));
                return;
            }
        }
        // Struct field array .len()
        if let ExprKind::Field { object: obj, field } = &object.kind
            && let ExprKind::Ident(obj_ident) = &obj.kind
        {
            let field_name = format!("{}_{}", obj_ident.name, field.name);
            if let Some(size) = self.array_sizes.get(&field_name) {
                self.write(&format!("{}", size));
                return;
            }
            // Check struct_field_array_sizes
            if let Some(size) = self.struct_field_array_sizes.get(&field_name) {
                self.write(&format!("{}", size));
                return;
            }
            // Look up struct definition
            if let Some(struct_name) = self.var_types.get(&obj_ident.name).cloned()
                && let Some(fields) = self.struct_defs.get(&struct_name)
            {
                for f in fields {
                    if f.name == field.name
                        && let Some(sz) = Self::get_array_size(&f.ty)
                    {
                        self.write(&format!("{}", sz));
                        return;
                    }
                }
            }
        }
        // Fallback: just use 0 (shouldn't happen for well-typed code)
        self.write("0 /* unknown len */");
    }

    fn generate_match_as_ternary(&mut self, expr: &Expr, arms: &[crate::parser::MatchArm]) {
        if arms.is_empty() {
            self.write("0");
            return;
        }
        for (i, arm) in arms.iter().enumerate() {
            let is_last = i == arms.len() - 1;
            let is_wildcard = matches!(arm.pattern.kind, crate::parser::PatternKind::Wildcard);

            if is_wildcard || is_last {
                self.generate_expr(&arm.body);
                return;
            }

            self.write("(");
            self.generate_pattern_condition(&arm.pattern, expr);
            self.write(" ? ");
            self.generate_expr(&arm.body);
            self.write(" : ");
        }
        self.write("0");
        for _ in 0..arms.len().saturating_sub(1) {
            self.write(")");
        }
    }

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
        use crate::parser::PrimitiveType;

        match &ty.kind {
            TypeKind::Primitive(p) => {
                let native = p.to_native();
                let bits = native.bit_width();

                // Check for endian read: buf[offset..offset+N] as u32be
                if let ExprKind::Slice { array, start, .. } = &expr.kind {
                    let is_be = matches!(
                        p,
                        PrimitiveType::U16Be
                            | PrimitiveType::U32Be
                            | PrimitiveType::U64Be
                            | PrimitiveType::U128Be
                            | PrimitiveType::I16Be
                            | PrimitiveType::I32Be
                            | PrimitiveType::I64Be
                            | PrimitiveType::I128Be
                    );
                    let is_le = matches!(
                        p,
                        PrimitiveType::U16Le
                            | PrimitiveType::U32Le
                            | PrimitiveType::U64Le
                            | PrimitiveType::U128Le
                            | PrimitiveType::I16Le
                            | PrimitiveType::I32Le
                            | PrimitiveType::I64Le
                            | PrimitiveType::I128Le
                    );
                    if is_be || is_le {
                        // Generate byte read
                        self.generate_endian_read(array, start, bits, is_be);
                        return;
                    }
                }

                match native {
                    PrimitiveType::Bool => {
                        self.write("(|");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    _ => {
                        // For narrowing: use masking (bit-select doesn't work on expressions in Verilog-2001)
                        // For widening: Verilog auto-extends
                        if bits < 32 {
                            let mask = (1u64 << bits) - 1;
                            self.write("(");
                            self.generate_expr(expr);
                            self.write(&format!(" & {}'h{:X})", bits, mask));
                        } else {
                            self.generate_expr(expr);
                        }
                    }
                }
            }
            TypeKind::Array { element, size } => {
                let elem_bits = self.type_bit_width(element);
                let total_bits = elem_bits * (*size as u32);
                if total_bits > 1 && total_bits < 128 {
                    let mask = if total_bits < 64 {
                        (1u128 << total_bits) - 1
                    } else {
                        u128::MAX >> (128 - total_bits)
                    };
                    self.write("(");
                    self.generate_expr(expr);
                    self.write(&format!(" & {}'h{:X})", total_bits, mask));
                } else {
                    self.generate_expr(expr);
                }
            }
            _ => {
                self.generate_expr(expr);
            }
        }
    }

    /// Generate endian byte read: read bytes from array and assemble into integer
    fn generate_endian_read(&mut self, array: &Expr, start: &Expr, bits: u32, is_be: bool) {
        let num_bytes = bits / 8;
        self.write("{");
        for i in 0..num_bytes {
            if i > 0 {
                self.write(", ");
            }
            let byte_idx = if is_be { i } else { num_bytes - 1 - i };
            self.generate_expr(array);
            self.write("[");
            self.generate_expr(start);
            if byte_idx > 0 {
                self.write(&format!(" + {}", byte_idx));
            }
            self.write("]");
        }
        self.write("}");
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
        match &ty.kind {
            TypeKind::Primitive(p) => {
                let bits = p.to_native().bit_width();
                if bits == 1 {
                    "1'b0".to_string()
                } else {
                    "0".to_string()
                }
            }
            TypeKind::Array { .. } => "0".to_string(),
            TypeKind::Named(_) => "0".to_string(),
            _ => "0".to_string(),
        }
    }

    /// Convert an expression to a string (for collecting array constant values)
    fn expr_to_string(&self, expr: &Expr) -> String {
        match &expr.kind {
            ExprKind::Integer(n) => {
                if *n == 0 {
                    "0".to_string()
                } else if *n <= 0xFFFF_FFFF {
                    format!("32'h{:08X}", n)
                } else if *n <= 0xFFFF_FFFF_FFFF_FFFF {
                    format!("64'h{:016X}", n)
                } else {
                    format!("128'h{:032X}", n)
                }
            }
            ExprKind::Bool(b) => {
                if *b {
                    "1'b1".to_string()
                } else {
                    "1'b0".to_string()
                }
            }
            _ => "0".to_string(),
        }
    }

    /// Generate inline runtime functions needed by the code
    fn generate_runtime_functions(&mut self) {
        // rotr and rotl are inlined at call sites, no separate function needed
        // But we need read_u32_be, write_u32_be etc. as functions if they're called

        // Generate rotr function (for cases where it's called by name)
        self.writeln("function [31:0] rotr;");
        self.indent();
        self.writeln("input [31:0] x;");
        self.writeln("input [31:0] n;");
        self.writeln("begin");
        self.writeln("  rotr = (x >> n) | (x << (32 - n));");
        self.writeln("end");
        self.dedent();
        self.writeln("endfunction");
        self.writeln("");

        self.writeln("function [31:0] rotl;");
        self.indent();
        self.writeln("input [31:0] x;");
        self.writeln("input [31:0] n;");
        self.writeln("begin");
        self.writeln("  rotl = (x << n) | (x >> (32 - n));");
        self.writeln("end");
        self.dedent();
        self.writeln("endfunction");
        self.writeln("");
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
        self.array_sizes.clear();
        self.array_consts.clear();
        self.known_tasks.clear();
        self.current_struct_name = None;
        self.stubbed_functions.clear();
        self.stubbed_tests.clear();
        self.unsupported_structs.clear();
        self.generated_functions.clear();
        self.struct_field_array_sizes.clear();
        self.func_param_info.clear();

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

                    // Check if struct has slice fields (unsupported)
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
                        methods.insert(method.name.name.clone(), mangled.clone());
                        // Check if it's a void function (task)
                        if method.return_type.is_none() {
                            self.known_tasks.insert(mangled);
                        }
                        // Static constructors returning Self become tasks
                        if method.is_static
                            && method.return_type.as_ref().is_some_and(|rt| {
                                matches!(&rt.kind, TypeKind::SelfType)
                                    || matches!(&rt.kind, TypeKind::Named(ident) if ident.name == "Self")
                            })
                        {
                            self.known_tasks
                                .insert(format!("{}__{}", impl_def.target.name, method.name.name));
                        }
                    }
                    self.struct_methods
                        .insert(impl_def.target.name.clone(), methods);
                }
                ItemKind::Function(func) => {
                    if func.return_type.is_none() {
                        self.known_tasks.insert(func.name.name.clone());
                    }
                    // Record array parameter sizes
                    for param in &func.params {
                        if let Some(sz) = Self::get_array_size(&param.ty) {
                            self.array_sizes.insert(param.name.name.clone(), sz);
                        }
                    }
                }
                _ => {}
            }
        }

        // Pre-pass 2: Identify functions that use unsupported features
        for item in &ast.ast.items {
            if let ItemKind::Function(func) = &item.kind
                && !Self::is_runtime_function(&func.name.name)
                && self.function_uses_unsupported_features(func)
            {
                self.stubbed_functions.insert(func.name.name.clone());
            }
        }

        // Pre-pass 3: Identify tests that use unsupported features
        for item in &ast.ast.items {
            if let ItemKind::Test(test) = &item.kind
                && self.block_uses_unsupported(&test.body)
            {
                self.stubbed_tests.insert(test.name.name.clone());
            }
        }

        // Emit header
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

        // Generate inline runtime functions
        self.generate_runtime_functions();

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

        // Generate initial block for test runner and array constant initialization
        if self.include_tests {
            self.writeln("// Test Runner");
            self.writeln("initial begin");
            self.indent();

            // Initialize array constants
            let consts = self.array_consts.clone();
            for ac in &consts {
                self.writeln(&format!("// Initialize {}", ac.name));
                for (i, val) in ac.values.iter().enumerate() {
                    self.writeln(&format!("{}[{}] = {};", ac.name, i, val));
                }
                self.writeln("");
            }

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
            self.writeln("if (__failed > 0) $finish(1);");
            self.writeln("else $finish;");
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
