//! JavaScript code generator
//!
//! Generates JavaScript code from the analyzed AST.
//! Uses TypedArrays for byte buffers and handles bitwise operations.

use crate::analysis::{AnalyzedAst, Type, TypeKind};
use crate::errors::AlgocResult;
use crate::parser::{
    Ast, Item, ItemKind, Function, Stmt, StmtKind, Expr, ExprKind,
    BinaryOp, UnaryOp, BuiltinFunc, Block,
};
use super::CodeGenerator;

/// JavaScript code generator
pub struct JavaScriptGenerator {
    /// Current indentation level
    indent: usize,
    /// Output buffer
    output: String,
}

impl JavaScriptGenerator {
    pub fn new() -> Self {
        Self {
            indent: 0,
            output: String::new(),
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

        // Rotate right for 32-bit values
        self.writeln("function rotr32(x, n) {");
        self.indent();
        self.writeln("return ((x >>> n) | (x << (32 - n))) >>> 0;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Rotate left for 32-bit values
        self.writeln("function rotl32(x, n) {");
        self.indent();
        self.writeln("return ((x << n) | (x >>> (32 - n))) >>> 0;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Read u32 big-endian
        self.writeln("function read_u32_be(buf, offset) {");
        self.indent();
        self.writeln("return ((buf[offset] << 24) | (buf[offset + 1] << 16) | (buf[offset + 2] << 8) | buf[offset + 3]) >>> 0;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Read u32 little-endian
        self.writeln("function read_u32_le(buf, offset) {");
        self.indent();
        self.writeln("return ((buf[offset + 3] << 24) | (buf[offset + 2] << 16) | (buf[offset + 1] << 8) | buf[offset]) >>> 0;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Write u32 big-endian
        self.writeln("function write_u32_be(buf, offset, value) {");
        self.indent();
        self.writeln("buf[offset] = (value >>> 24) & 0xff;");
        self.writeln("buf[offset + 1] = (value >>> 16) & 0xff;");
        self.writeln("buf[offset + 2] = (value >>> 8) & 0xff;");
        self.writeln("buf[offset + 3] = value & 0xff;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Write u32 little-endian
        self.writeln("function write_u32_le(buf, offset, value) {");
        self.indent();
        self.writeln("buf[offset] = value & 0xff;");
        self.writeln("buf[offset + 1] = (value >>> 8) & 0xff;");
        self.writeln("buf[offset + 2] = (value >>> 16) & 0xff;");
        self.writeln("buf[offset + 3] = (value >>> 24) & 0xff;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Write u64 big-endian (using BigInt internally but storing as bytes)
        self.writeln("function write_u64_be(buf, offset, value) {");
        self.indent();
        self.writeln("const hi = Math.floor(value / 0x100000000);");
        self.writeln("const lo = value >>> 0;");
        self.writeln("write_u32_be(buf, offset, hi);");
        self.writeln("write_u32_be(buf, offset + 4, lo);");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Secure zero (best effort in JS)
        self.writeln("function secure_zero(buf) {");
        self.indent();
        self.writeln("if (buf instanceof Uint8Array || buf instanceof Uint32Array) {");
        self.indent();
        self.writeln("buf.fill(0);");
        self.dedent();
        self.writeln("} else if (Array.isArray(buf)) {");
        self.indent();
        self.writeln("buf.fill(0);");
        self.dedent();
        self.writeln("}");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Constant-time comparison
        self.writeln("function constant_time_eq(a, b) {");
        self.indent();
        self.writeln("if (a.length !== b.length) return false;");
        self.writeln("let result = 0;");
        self.writeln("for (let i = 0; i < a.length; i++) {");
        self.indent();
        self.writeln("result |= a[i] ^ b[i];");
        self.dedent();
        self.writeln("}");
        self.writeln("return result === 0;");
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
            ItemKind::Test(_) => {
                // Tests are generated separately
            }
        }
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        self.write_indent();
        self.write(&format!("const {} = ", c.name.name));
        self.generate_expr(&c.value);
        self.write(";\n\n");
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Generate a factory function for the struct
        self.writeln(&format!("function create_{}() {{", s.name.name));
        self.indent();
        self.writeln("return {");
        self.indent();
        for (i, field) in s.fields.iter().enumerate() {
            let comma = if i < s.fields.len() - 1 { "," } else { "" };
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{}: {}{}", field.name.name, init, comma));
        }
        self.dedent();
        self.writeln("};");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs
        self.writeln(&format!("function create_{}() {{", l.name.name));
        self.indent();
        self.writeln("return {");
        self.indent();
        for (i, field) in l.fields.iter().enumerate() {
            let comma = if i < l.fields.len() - 1 { "," } else { "" };
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{}: {}{}", field.name.name, init, comma));
        }
        self.dedent();
        self.writeln("};");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn default_value_for_type(&self, ty: &crate::parser::Type) -> String {
        match &ty.kind {
            crate::parser::TypeKind::Primitive(_) => "0".to_string(),
            crate::parser::TypeKind::Array { element, size } => {
                match &element.kind {
                    crate::parser::TypeKind::Primitive(p) => {
                        match p {
                            crate::parser::PrimitiveType::U8 => format!("new Uint8Array({})", size),
                            crate::parser::PrimitiveType::U16 => format!("new Uint16Array({})", size),
                            crate::parser::PrimitiveType::U32 => format!("new Uint32Array({})", size),
                            _ => format!("new Array({}).fill(0)", size),
                        }
                    }
                    _ => format!("new Array({}).fill(0)", size),
                }
            }
            crate::parser::TypeKind::Named(ident) => {
                // Struct type - call factory function
                format!("create_{}()", ident.name)
            }
            _ => "null".to_string(),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        self.write_indent();
        self.write(&format!("function {}(", func.name.name));

        // Parameters
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&param.name.name);
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
                self.write_indent();
                self.write(&format!("let {} = ", name.name));
                if let Some(init) = init {
                    self.generate_expr(init);
                } else if let Some(ty) = ty {
                    self.write(&self.default_value_for_type(ty));
                } else {
                    self.write("undefined");
                }
                self.write(";\n");
            }
            StmtKind::Expr(expr) => {
                self.write_indent();
                self.generate_expr(expr);
                self.write(";\n");
            }
            StmtKind::Assign { target, value } => {
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
                    BinaryOp::Shr => ">>>=",
                    _ => "=",
                };
                self.write(&format!(" {} ", op_str));
                self.generate_expr(value);
                self.write(";\n");
            }
            StmtKind::If { condition, then_block, else_block } => {
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
            StmtKind::For { var, start, end, inclusive, body } => {
                self.write_indent();
                self.write(&format!("for (let {} = ", var.name));
                self.generate_expr(start);
                self.write(&format!("; {} {} ", var.name, if *inclusive { "<=" } else { "<" }));
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
                // For values that fit in 32 bits, use regular numbers
                // For larger values, we'd use BigInt but our DSL mostly uses 32-bit
                if *n <= u32::MAX as u128 {
                    self.write(&format!("{}", n));
                } else {
                    self.write(&format!("{}n", n));
                }
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "true" } else { "false" });
            }
            ExprKind::String(s) => {
                // Convert string to Uint8Array
                self.write(&format!("new TextEncoder().encode(\"{}\")", escape_js_string(s)));
            }
            ExprKind::Bytes(s) => {
                self.write(&format!("new TextEncoder().encode(\"{}\")", escape_js_string(s)));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to Uint8Array
                self.write(&format!("Uint8Array.from('{}'.match(/.{{2}}/g).map(b => parseInt(b, 16)))", h));
            }
            ExprKind::Ident(ident) => {
                self.write(&ident.name);
            }
            ExprKind::Binary { left, op, right } => {
                // For bitwise operations on 32-bit values, we need >>> 0 to ensure unsigned
                let needs_unsigned = matches!(op,
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul |
                    BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor |
                    BinaryOp::Shl | BinaryOp::Shr
                );

                if needs_unsigned {
                    self.write("(");
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
                    BinaryOp::Shr => " >>> ", // Unsigned right shift
                    BinaryOp::Eq => " === ",
                    BinaryOp::Ne => " !== ",
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
                if needs_unsigned {
                    self.write(" >>> 0)");
                }
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
                // For bitwise not, ensure unsigned
                if matches!(op, UnaryOp::BitNot) {
                    self.write(" >>> 0");
                }
            }
            ExprKind::Index { array, index } => {
                self.generate_expr(array);
                self.write("[");
                self.generate_expr(index);
                self.write("]");
            }
            ExprKind::Slice { array, start, end, .. } => {
                self.generate_expr(array);
                self.write(".subarray(");
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
                // Check for method calls like slice.len()
                if let ExprKind::Field { object, field } = &func.kind {
                    if field.name == "len" && args.is_empty() {
                        // Convert .len() to .length
                        self.generate_expr(object);
                        self.write(".length");
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
                // Generate as typed array if possible
                if elements.is_empty() {
                    self.write("[]");
                } else {
                    // Check if all elements are integers
                    let all_ints = elements.iter().all(|e| matches!(e.kind, ExprKind::Integer(_)));
                    if all_ints {
                        self.write("new Uint32Array([");
                    } else {
                        self.write("[");
                    }
                    for (i, elem) in elements.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(elem);
                    }
                    if all_ints {
                        self.write("])");
                    } else {
                        self.write("]");
                    }
                }
            }
            ExprKind::Cast { expr, .. } => {
                // In JavaScript, casts are mostly no-ops for numeric types
                // For now, just generate the expression
                self.generate_expr(expr);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in JS are just the value (pass by reference for objects)
                self.generate_expr(inner);
            }
            ExprKind::Deref(inner) => {
                // Dereferences are also no-ops in JS
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
                self.write("{ ");
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("{}: ", field_name.name));
                    self.generate_expr(value);
                }
                self.write(" }");
            }
        }
    }

    fn generate_builtin(&mut self, name: BuiltinFunc, args: &[Expr]) {
        match name {
            BuiltinFunc::Rotr => {
                self.write("rotr32(");
                self.generate_expr(&args[0]);
                self.write(", ");
                self.generate_expr(&args[1]);
                self.write(")");
            }
            BuiltinFunc::Rotl => {
                self.write("rotl32(");
                self.generate_expr(&args[0]);
                self.write(", ");
                self.generate_expr(&args[1]);
                self.write(")");
            }
            BuiltinFunc::Bswap => {
                // Byte swap for 32-bit
                self.write("(((");
                self.generate_expr(&args[0]);
                self.write(" & 0xff) << 24) | ((");
                self.generate_expr(&args[0]);
                self.write(" & 0xff00) << 8) | ((");
                self.generate_expr(&args[0]);
                self.write(" & 0xff0000) >>> 8) | ((");
                self.generate_expr(&args[0]);
                self.write(" & 0xff000000) >>> 24))");
            }
            BuiltinFunc::ReadU8 => {
                self.generate_expr(&args[0]);
                self.write("[");
                self.generate_expr(&args[1]);
                self.write("]");
            }
            BuiltinFunc::ReadU16Be => {
                self.write("((");
                self.generate_expr(&args[0]);
                self.write("[");
                self.generate_expr(&args[1]);
                self.write("] << 8) | ");
                self.generate_expr(&args[0]);
                self.write("[");
                self.generate_expr(&args[1]);
                self.write(" + 1])");
            }
            BuiltinFunc::ReadU16Le => {
                self.write("(");
                self.generate_expr(&args[0]);
                self.write("[");
                self.generate_expr(&args[1]);
                self.write("] | (");
                self.generate_expr(&args[0]);
                self.write("[");
                self.generate_expr(&args[1]);
                self.write(" + 1] << 8))");
            }
            BuiltinFunc::ReadU32Be => {
                self.write("read_u32_be(");
                self.generate_expr(&args[0]);
                self.write(", ");
                self.generate_expr(&args[1]);
                self.write(")");
            }
            BuiltinFunc::ReadU32Le => {
                self.write("read_u32_le(");
                self.generate_expr(&args[0]);
                self.write(", ");
                self.generate_expr(&args[1]);
                self.write(")");
            }
            BuiltinFunc::ReadU64Be | BuiltinFunc::ReadU64Le => {
                // For 64-bit reads, use BigInt
                self.write("/* TODO: 64-bit read */0");
            }
            BuiltinFunc::WriteU8 => {
                self.generate_expr(&args[0]);
                self.write("[");
                self.generate_expr(&args[1]);
                self.write("] = ");
                self.generate_expr(&args[2]);
            }
            BuiltinFunc::WriteU16Be | BuiltinFunc::WriteU16Le => {
                // Inline 16-bit write
                self.write("/* TODO: 16-bit write */");
            }
            BuiltinFunc::WriteU32Be => {
                self.write("write_u32_be(");
                self.generate_expr(&args[0]);
                self.write(", ");
                self.generate_expr(&args[1]);
                self.write(", ");
                self.generate_expr(&args[2]);
                self.write(")");
            }
            BuiltinFunc::WriteU32Le => {
                self.write("write_u32_le(");
                self.generate_expr(&args[0]);
                self.write(", ");
                self.generate_expr(&args[1]);
                self.write(", ");
                self.generate_expr(&args[2]);
                self.write(")");
            }
            BuiltinFunc::WriteU64Be => {
                self.write("write_u64_be(");
                self.generate_expr(&args[0]);
                self.write(", ");
                self.generate_expr(&args[1]);
                self.write(", ");
                self.generate_expr(&args[2]);
                self.write(")");
            }
            BuiltinFunc::WriteU64Le => {
                self.write("/* TODO: write_u64_le */");
            }
            BuiltinFunc::ConstantTimeEq => {
                self.write("constant_time_eq(");
                self.generate_expr(&args[0]);
                self.write(", ");
                self.generate_expr(&args[1]);
                self.write(")");
            }
            BuiltinFunc::SecureZero => {
                self.write("secure_zero(");
                self.generate_expr(&args[0]);
                self.write(")");
            }
        }
    }
}

impl Default for JavaScriptGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for JavaScriptGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();

        self.writeln("// Generated by AlgoC");
        self.writeln("// DO NOT EDIT - This file is auto-generated");
        self.writeln("");

        self.generate_runtime();
        self.generate_ast(&ast.ast);

        // Export functions
        self.writeln("// Exports");
        self.writeln("if (typeof module !== 'undefined' && module.exports) {");
        self.indent();
        self.write_indent();
        self.write("module.exports = { ");
        let mut first = true;
        for item in &ast.ast.items {
            if let ItemKind::Function(func) = &item.kind {
                if !first {
                    self.write(", ");
                }
                self.write(&func.name.name);
                first = false;
            }
        }
        self.write(" };\n");
        self.dedent();
        self.writeln("}");

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "js"
    }

    fn language_name(&self) -> &'static str {
        "JavaScript"
    }
}

fn escape_js_string(s: &str) -> String {
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
