//! Perl code generator
//!
//! Generates Perl code from the analyzed AST.
//! Uses regular arrays of integers for byte buffers and handles bitwise operations
//! with explicit masking since Perl integers have platform-dependent width.

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

/// Perl code generator
pub struct PerlGenerator {
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
    /// Variable element types for arrays/slices (for correct integer masking on assignment)
    var_elem_types: HashMap<String, PrimitiveType>,
}

impl PerlGenerator {
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

    /// Extract the element primitive type from a parser type, unwrapping references/arrays/slices.
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

    /// Generate the runtime helper functions
    fn generate_runtime(&mut self) {
        self.writeln("# AlgoC Runtime Helpers");
        self.writeln("");

        // Masking helpers
        self.writeln("sub _u8 { return $_[0] & 0xFF; }");
        self.writeln("sub _u16 { return $_[0] & 0xFFFF; }");
        self.writeln("sub _u32 { return $_[0] & 0xFFFFFFFF; }");
        self.writeln("sub _u64 { return $_[0] & 0xFFFFFFFFFFFFFFFF; }");
        self.writeln("");

        // Reader package for streaming byte input
        self.writeln("{");
        self.indent();
        self.writeln("package Reader;");
        self.writeln("sub new {");
        self.indent();
        self.writeln("my ($class, $data) = @_;");
        self.writeln("return bless { data => $data, pos => 0 }, $class;");
        self.dedent();
        self.writeln("}");

        // read_u8
        self.writeln("sub read_u8 {");
        self.indent();
        self.writeln("my ($self) = @_;");
        self.writeln("die 'EOF' if $self->{pos} >= scalar(@{$self->{data}});");
        self.writeln("return $self->{data}[$self->{pos}++];");
        self.dedent();
        self.writeln("}");

        // read_u16 variants
        self.writeln("sub read_u16 { return $_[0]->read_u16be(); }");
        self.writeln("sub read_u16be {");
        self.indent();
        self.writeln("my ($self) = @_;");
        self.writeln("die 'EOF' if $self->{pos} + 2 > scalar(@{$self->{data}});");
        self.writeln(
            "my $v = ($self->{data}[$self->{pos}] << 8) | $self->{data}[$self->{pos} + 1];",
        );
        self.writeln("$self->{pos} += 2;");
        self.writeln("return $v;");
        self.dedent();
        self.writeln("}");
        self.writeln("sub read_u16le {");
        self.indent();
        self.writeln("my ($self) = @_;");
        self.writeln("die 'EOF' if $self->{pos} + 2 > scalar(@{$self->{data}});");
        self.writeln(
            "my $v = $self->{data}[$self->{pos}] | ($self->{data}[$self->{pos} + 1] << 8);",
        );
        self.writeln("$self->{pos} += 2;");
        self.writeln("return $v;");
        self.dedent();
        self.writeln("}");

        // read_u32 variants
        self.writeln("sub read_u32 { return $_[0]->read_u32be(); }");
        self.writeln("sub read_u32be {");
        self.indent();
        self.writeln("my ($self) = @_;");
        self.writeln("die 'EOF' if $self->{pos} + 4 > scalar(@{$self->{data}});");
        self.writeln("my $v = ($self->{data}[$self->{pos}] << 24) | ($self->{data}[$self->{pos} + 1] << 16) | ($self->{data}[$self->{pos} + 2] << 8) | $self->{data}[$self->{pos} + 3];");
        self.writeln("$self->{pos} += 4;");
        self.writeln("return $v & 0xFFFFFFFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("sub read_u32le {");
        self.indent();
        self.writeln("my ($self) = @_;");
        self.writeln("die 'EOF' if $self->{pos} + 4 > scalar(@{$self->{data}});");
        self.writeln("my $v = $self->{data}[$self->{pos}] | ($self->{data}[$self->{pos} + 1] << 8) | ($self->{data}[$self->{pos} + 2] << 16) | ($self->{data}[$self->{pos} + 3] << 24);");
        self.writeln("$self->{pos} += 4;");
        self.writeln("return $v & 0xFFFFFFFF;");
        self.dedent();
        self.writeln("}");

        // read_u64 variants
        self.writeln("sub read_u64 { return $_[0]->read_u64be(); }");
        self.writeln("sub read_u64be {");
        self.indent();
        self.writeln("my ($self) = @_;");
        self.writeln("die 'EOF' if $self->{pos} + 8 > scalar(@{$self->{data}});");
        self.writeln("my $v = 0;");
        self.writeln("for my $i (0..7) { $v = ($v << 8) | $self->{data}[$self->{pos} + $i]; }");
        self.writeln("$self->{pos} += 8;");
        self.writeln("return $v & 0xFFFFFFFFFFFFFFFF;");
        self.dedent();
        self.writeln("}");
        self.writeln("sub read_u64le {");
        self.indent();
        self.writeln("my ($self) = @_;");
        self.writeln("die 'EOF' if $self->{pos} + 8 > scalar(@{$self->{data}});");
        self.writeln("my $v = 0;");
        self.writeln(
            "for my $i (reverse 0..7) { $v = ($v << 8) | $self->{data}[$self->{pos} + $i]; }",
        );
        self.writeln("$self->{pos} += 8;");
        self.writeln("return $v & 0xFFFFFFFFFFFFFFFF;");
        self.dedent();
        self.writeln("}");

        // read_bytes
        self.writeln("sub read_bytes {");
        self.indent();
        self.writeln("my ($self, $count) = @_;");
        self.writeln("die 'EOF' if $self->{pos} + $count > scalar(@{$self->{data}});");
        self.writeln("my @result = @{$self->{data}}[$self->{pos} .. $self->{pos} + $count - 1];");
        self.writeln("$self->{pos} += $count;");
        self.writeln("return \\@result;");
        self.dedent();
        self.writeln("}");

        // read_chunk
        self.writeln("sub read_chunk {");
        self.indent();
        self.writeln("my ($self, $max_size) = @_;");
        self.writeln("my $remaining = scalar(@{$self->{data}}) - $self->{pos};");
        self.writeln("my $count = $max_size < $remaining ? $max_size : $remaining;");
        self.writeln("if ($count <= 0) { return []; }");
        self.writeln("my @result = @{$self->{data}}[$self->{pos} .. $self->{pos} + $count - 1];");
        self.writeln("$self->{pos} += $count;");
        self.writeln("return \\@result;");
        self.dedent();
        self.writeln("}");

        // eof
        self.writeln("sub eof { return $_[0]->{pos} >= scalar(@{$_[0]->{data}}) ? 1 : 0; }");

        self.dedent();
        self.writeln("}");
        self.writeln("");

        // Writer package for streaming byte output
        self.writeln("{");
        self.indent();
        self.writeln("package Writer;");
        self.writeln("sub new {");
        self.indent();
        self.writeln("my ($class, $data) = @_;");
        self.writeln("return bless { data => $data, pos => 0 }, $class;");
        self.dedent();
        self.writeln("}");

        // write_u8
        self.writeln("sub write_u8 {");
        self.indent();
        self.writeln("my ($self, $v) = @_;");
        self.writeln("die 'Buffer overflow' if $self->{pos} >= scalar(@{$self->{data}});");
        self.writeln("$self->{data}[$self->{pos}++] = $v & 0xFF;");
        self.dedent();
        self.writeln("}");

        // write_u16 variants
        self.writeln("sub write_u16 { $_[0]->write_u16be($_[1]); }");
        self.writeln("sub write_u16be {");
        self.indent();
        self.writeln("my ($self, $v) = @_;");
        self.writeln("die 'Buffer overflow' if $self->{pos} + 2 > scalar(@{$self->{data}});");
        self.writeln("$self->{data}[$self->{pos}] = ($v >> 8) & 0xFF;");
        self.writeln("$self->{data}[$self->{pos} + 1] = $v & 0xFF;");
        self.writeln("$self->{pos} += 2;");
        self.dedent();
        self.writeln("}");
        self.writeln("sub write_u16le {");
        self.indent();
        self.writeln("my ($self, $v) = @_;");
        self.writeln("die 'Buffer overflow' if $self->{pos} + 2 > scalar(@{$self->{data}});");
        self.writeln("$self->{data}[$self->{pos}] = $v & 0xFF;");
        self.writeln("$self->{data}[$self->{pos} + 1] = ($v >> 8) & 0xFF;");
        self.writeln("$self->{pos} += 2;");
        self.dedent();
        self.writeln("}");

        // write_u32 variants
        self.writeln("sub write_u32 { $_[0]->write_u32be($_[1]); }");
        self.writeln("sub write_u32be {");
        self.indent();
        self.writeln("my ($self, $v) = @_;");
        self.writeln("die 'Buffer overflow' if $self->{pos} + 4 > scalar(@{$self->{data}});");
        self.writeln("$self->{data}[$self->{pos}] = ($v >> 24) & 0xFF;");
        self.writeln("$self->{data}[$self->{pos} + 1] = ($v >> 16) & 0xFF;");
        self.writeln("$self->{data}[$self->{pos} + 2] = ($v >> 8) & 0xFF;");
        self.writeln("$self->{data}[$self->{pos} + 3] = $v & 0xFF;");
        self.writeln("$self->{pos} += 4;");
        self.dedent();
        self.writeln("}");
        self.writeln("sub write_u32le {");
        self.indent();
        self.writeln("my ($self, $v) = @_;");
        self.writeln("die 'Buffer overflow' if $self->{pos} + 4 > scalar(@{$self->{data}});");
        self.writeln("$self->{data}[$self->{pos}] = $v & 0xFF;");
        self.writeln("$self->{data}[$self->{pos} + 1] = ($v >> 8) & 0xFF;");
        self.writeln("$self->{data}[$self->{pos} + 2] = ($v >> 16) & 0xFF;");
        self.writeln("$self->{data}[$self->{pos} + 3] = ($v >> 24) & 0xFF;");
        self.writeln("$self->{pos} += 4;");
        self.dedent();
        self.writeln("}");

        // write_u64 variants
        self.writeln("sub write_u64 { $_[0]->write_u64be($_[1]); }");
        self.writeln("sub write_u64be {");
        self.indent();
        self.writeln("my ($self, $v) = @_;");
        self.writeln("die 'Buffer overflow' if $self->{pos} + 8 > scalar(@{$self->{data}});");
        self.writeln(
            "for my $i (0..7) { $self->{data}[$self->{pos} + $i] = ($v >> (56 - $i * 8)) & 0xFF; }",
        );
        self.writeln("$self->{pos} += 8;");
        self.dedent();
        self.writeln("}");
        self.writeln("sub write_u64le {");
        self.indent();
        self.writeln("my ($self, $v) = @_;");
        self.writeln("die 'Buffer overflow' if $self->{pos} + 8 > scalar(@{$self->{data}});");
        self.writeln(
            "for my $i (0..7) { $self->{data}[$self->{pos} + $i] = ($v >> ($i * 8)) & 0xFF; }",
        );
        self.writeln("$self->{pos} += 8;");
        self.dedent();
        self.writeln("}");

        // write_bytes
        self.writeln("sub write_bytes {");
        self.indent();
        self.writeln("my ($self, $data) = @_;");
        self.writeln(
            "die 'Buffer overflow' if $self->{pos} + scalar(@$data) > scalar(@{$self->{data}});",
        );
        self.writeln(
            "for my $i (0 .. $#$data) { $self->{data}[$self->{pos} + $i] = $data->[$i]; }",
        );
        self.writeln("$self->{pos} += scalar(@$data);");
        self.dedent();
        self.writeln("}");

        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    /// Generate test runtime helpers (only when include_tests is true)
    fn generate_test_runtime(&mut self) {
        self.writeln("# Test Helpers");
        self.writeln("");

        self.writeln("my $__test_failures = 0;");
        self.writeln("my $__test_name = '';");
        self.writeln("");

        self.writeln("sub __assert {");
        self.indent();
        self.writeln("my ($condition) = @_;");
        self.writeln("if (!$condition) {");
        self.indent();
        self.writeln("$__test_failures++;");
        self.writeln("print \"  ASSERTION FAILED in $__test_name\\n\";");
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
        let params: Vec<String> = func
            .params
            .iter()
            .map(|p| format!("${}", p.name.name))
            .collect();

        self.writeln(&format!("sub {} {{", mangled_name));
        self.indent();
        self.writeln(&format!("my ({}) = @_;", params.join(", ")));
        self.generate_block(&func.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_test(&mut self, test: &crate::parser::TestDef) {
        self.writeln(&format!("sub test_{} {{", test.name.name));
        self.indent();
        self.generate_block(&test.body);
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_const(&mut self, c: &crate::parser::ConstDef) {
        // For array constants, use my @NAME = (...);
        // For scalar constants, use use constant or my $NAME = ...;
        match &c.value.kind {
            ExprKind::Array(_) => {
                self.write_indent();
                self.write(&format!("my @{} = ", c.name.name));
                // Generate array elements without the [] wrapper
                if let ExprKind::Array(elements) = &c.value.kind {
                    self.write("(");
                    for (i, elem) in elements.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.generate_expr(elem);
                    }
                    self.write(")");
                }
                self.write(";\n\n");
            }
            _ => {
                self.write_indent();
                self.write(&format!("use constant {} => ", c.name.name));
                self.generate_expr(&c.value);
                self.write(";\n\n");
            }
        }
    }

    fn generate_struct(&mut self, s: &crate::parser::StructDef) {
        // Generate a factory function that returns a hash ref
        self.writeln(&format!("sub create_{} {{", s.name.name));
        self.indent();
        self.writeln("return {");
        self.indent();
        for (i, field) in s.fields.iter().enumerate() {
            let comma = if i < s.fields.len() - 1 { "," } else { "" };
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{} => {}{}", field.name.name, init, comma));
        }
        self.dedent();
        self.writeln("};");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_layout(&mut self, l: &crate::parser::LayoutDef) {
        // Layouts are similar to structs
        self.writeln(&format!("sub create_{} {{", l.name.name));
        self.indent();
        self.writeln("return {");
        self.indent();
        for (i, field) in l.fields.iter().enumerate() {
            let comma = if i < l.fields.len() - 1 { "," } else { "" };
            let init = self.default_value_for_type(&field.ty);
            self.writeln(&format!("{} => {}{}", field.name.name, init, comma));
        }
        self.dedent();
        self.writeln("};");
        self.dedent();
        self.writeln("}");
        self.writeln("");
    }

    fn generate_enum(&mut self, e: &crate::parser::EnumDef) {
        // Generate enum variants as factory functions in a hash
        // enum Color { Red, Green, Rgb(u8, u8, u8) }
        // becomes factory subs under the enum name
        for variant in &e.variants {
            match &variant.data {
                crate::parser::EnumVariantData::Unit => {
                    // Unit variant: constant hash ref
                    self.writeln(&format!(
                        "sub {}_{} {{ return {{ tag => '{}' }}; }}",
                        e.name.name, variant.name.name, variant.name.name
                    ));
                }
                crate::parser::EnumVariantData::Tuple(types) => {
                    // Tuple variant: factory function
                    let params: Vec<String> =
                        (0..types.len()).map(|i| format!("$v{}", i)).collect();
                    let params_str = params.join(", ");
                    let fields: Vec<String> = (0..types.len())
                        .map(|i| format!("v{} => $v{}", i, i))
                        .collect();
                    let fields_str = fields.join(", ");
                    self.writeln(&format!(
                        "sub {}_{} {{ my ({}) = @_; return {{ tag => '{}', {} }}; }}",
                        e.name.name, variant.name.name, params_str, variant.name.name, fields_str
                    ));
                }
                crate::parser::EnumVariantData::Struct(fields) => {
                    // Struct variant: factory function with named fields
                    let params: Vec<String> =
                        fields.iter().map(|f| format!("${}", f.name.name)).collect();
                    let params_str = params.join(", ");
                    let field_inits: Vec<String> = fields
                        .iter()
                        .map(|f| format!("{} => ${}", f.name.name, f.name.name))
                        .collect();
                    let fields_str = field_inits.join(", ");
                    self.writeln(&format!(
                        "sub {}_{} {{ my ({}) = @_; return {{ tag => '{}', {} }}; }}",
                        e.name.name, variant.name.name, params_str, variant.name.name, fields_str
                    ));
                }
            }
        }
        self.writeln("");
    }

    fn default_value_for_type(&self, ty: &crate::parser::Type) -> String {
        match &ty.kind {
            crate::parser::TypeKind::Primitive(_) => "0".to_string(),
            crate::parser::TypeKind::Array { element, size } => {
                if let crate::parser::TypeKind::Primitive(_) = &element.kind {
                    format!("[(0) x {}]", size)
                } else {
                    format!("[(0) x {}]", size)
                }
            }
            crate::parser::TypeKind::Named(ident) => {
                format!("create_{}()", ident.name)
            }
            _ => "undef".to_string(),
        }
    }

    fn generate_function(&mut self, func: &Function) {
        // Track parameter element types for correct masking
        let saved_elem_types = self.var_elem_types.clone();
        for param in &func.params {
            if let Some(elem_prim) = Self::element_primitive(&param.ty) {
                self.var_elem_types
                    .insert(param.name.name.clone(), elem_prim);
            }
        }

        self.write_indent();
        self.write(&format!("sub {} {{", func.name.name));
        self.write("\n");
        self.indent();

        // Parameters
        if !func.params.is_empty() {
            let params: Vec<String> = func
                .params
                .iter()
                .map(|p| format!("${}", p.name.name))
                .collect();
            self.writeln(&format!("my ({}) = @_;", params.join(", ")));
        }

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
            StmtKind::Let { name, ty, init, .. } => {
                // Track variable type for struct read/write generation
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

                // Determine if this is an array type that needs @
                let is_array_type = ty
                    .as_ref()
                    .map(|t| {
                        matches!(
                            t.kind,
                            crate::parser::TypeKind::Array { .. }
                                | crate::parser::TypeKind::Slice { .. }
                        )
                    })
                    .unwrap_or(false);

                // Check if init expr produces an array
                let init_is_array = init.as_ref().map(is_array_like_expr).unwrap_or(false);

                if is_array_type && !init_is_array {
                    // Array type with non-array init - use array ref
                    self.write_indent();
                    self.write(&format!("my ${} = ", name.name));
                    if let Some(init) = init {
                        self.generate_expr(init);
                    } else if let Some(ty) = ty {
                        self.write(&self.default_value_for_type(ty));
                    } else {
                        self.write("undef");
                    }
                    self.write(";\n");
                } else {
                    // Scalar variable
                    self.write_indent();
                    self.write(&format!("my ${} = ", name.name));
                    if let Some(init) = init {
                        self.generate_expr(init);
                    } else if let Some(ty) = ty {
                        self.write(&self.default_value_for_type(ty));
                    } else {
                        self.write("undef");
                    }
                    self.write(";\n");
                }
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
                        let byte_count = match p.to_native() {
                            crate::parser::PrimitiveType::U16
                            | crate::parser::PrimitiveType::I16 => 2,
                            crate::parser::PrimitiveType::U32
                            | crate::parser::PrimitiveType::I32 => 4,
                            crate::parser::PrimitiveType::U64
                            | crate::parser::PrimitiveType::I64 => 8,
                            crate::parser::PrimitiveType::U128
                            | crate::parser::PrimitiveType::I128 => 16,
                            _ => 4,
                        };
                        let is_little = endian == crate::parser::Endianness::Little;
                        self.write_indent();
                        self.write("do { my $__v = ");
                        self.generate_expr(value);
                        self.write("; my $__s = ");
                        self.generate_expr(start);
                        self.write("; ");
                        for i in 0..byte_count {
                            let shift = if is_little {
                                i * 8
                            } else {
                                (byte_count - 1 - i) * 8
                            };
                            self.generate_expr(array);
                            self.write(&format!("->[$__s + {}] = ($__v >> {}) & 0xFF; ", i, shift));
                        }
                        self.write("};\n");
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
                    BinaryOp::Add => " += ",
                    BinaryOp::Sub => " -= ",
                    BinaryOp::Mul => " *= ",
                    BinaryOp::Div => {
                        // Perl / is float division; use int()
                        self.write(" = int(");
                        self.generate_expr(target);
                        self.write(" / ");
                        self.generate_expr(value);
                        self.write(");\n");
                        return;
                    }
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
                self.write(&format!("for my ${} (", var.name));
                self.generate_expr(start);
                self.write(" .. ");
                if *inclusive {
                    self.generate_expr(end);
                } else {
                    self.generate_expr(end);
                    self.write(" - 1");
                }
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
                self.writeln("while (1) {");
                self.indent();
                self.generate_block(body);
                self.dedent();
                self.writeln("}");
            }
            StmtKind::Break => {
                self.writeln("last;");
            }
            StmtKind::Continue => {
                self.writeln("next;");
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

    fn generate_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Integer(n) => {
                self.write(&format!("{}", n));
            }
            ExprKind::Bool(b) => {
                self.write(if *b { "1" } else { "0" });
            }
            ExprKind::String(s) => {
                // Convert string to array of bytes
                let bytes: Vec<String> = s.bytes().map(|b| format!("{}", b)).collect();
                self.write(&format!("[{}]", bytes.join(", ")));
            }
            ExprKind::Bytes(s) => {
                let bytes: Vec<String> = s.bytes().map(|b| format!("{}", b)).collect();
                self.write(&format!("[{}]", bytes.join(", ")));
            }
            ExprKind::Hex(h) => {
                // Convert hex string to array of bytes
                let mut bytes = Vec::new();
                let chars: Vec<char> = h.chars().collect();
                for chunk in chars.chunks(2) {
                    let hex_str: String = chunk.iter().collect();
                    if let Ok(b) = u8::from_str_radix(&hex_str, 16) {
                        bytes.push(format!("{}", b));
                    }
                }
                self.write(&format!("[{}]", bytes.join(", ")));
            }
            ExprKind::Ident(ident) => {
                self.write(&format!("${}", ident.name));
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

                // Handle integer division specially - Perl / does float division
                if matches!(op, BinaryOp::Div) {
                    self.write("int(");
                    self.generate_expr(left);
                    self.write(" / ");
                    self.generate_expr(right);
                    self.write(")");
                    return;
                }

                // Perl integers are arbitrary precision in some cases, so mask for bitwise ops
                let uses_u64 = expr_uses_u64(left) || expr_uses_u64(right);
                let needs_mask = matches!(
                    op,
                    BinaryOp::Add
                        | BinaryOp::Sub
                        | BinaryOp::Mul
                        | BinaryOp::BitAnd
                        | BinaryOp::BitOr
                        | BinaryOp::BitXor
                        | BinaryOp::Shl
                        | BinaryOp::Shr
                );

                if needs_mask {
                    if uses_u64 {
                        self.write("_u64(");
                    } else {
                        self.write("_u32(");
                    }
                }
                self.write("(");
                self.generate_expr(left);
                let op_str = match op {
                    BinaryOp::Add => " + ",
                    BinaryOp::Sub => " - ",
                    BinaryOp::Mul => " * ",
                    BinaryOp::Div => unreachable!(), // handled above
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
                if needs_mask {
                    self.write(")");
                }
            }
            ExprKind::Unary { op, operand } => {
                match op {
                    UnaryOp::Neg => {
                        self.write("-(");
                        self.generate_expr(operand);
                        self.write(")");
                    }
                    UnaryOp::Not => {
                        self.write("!(");
                        self.generate_expr(operand);
                        self.write(")");
                    }
                    UnaryOp::BitNot => {
                        // Perl ~ on large integers needs masking
                        self.write("_u32(~(");
                        self.generate_expr(operand);
                        self.write("))");
                    }
                }
            }
            ExprKind::Index { array, index } => {
                self.generate_expr(array);
                self.write("->[");
                self.generate_expr(index);
                self.write("]");
            }
            ExprKind::Slice {
                array,
                start,
                end,
                inclusive,
            } => {
                // Perl array slices: [@{$arr}[$start .. $end-1]]
                // Return as array ref
                self.write("[@{");
                self.generate_expr(array);
                self.write("}[");
                self.generate_expr(start);
                self.write(" .. ");
                if *inclusive {
                    self.generate_expr(end);
                } else {
                    self.generate_expr(end);
                    self.write(" - 1");
                }
                self.write("]]");
            }
            ExprKind::Field { object, field } => {
                self.generate_expr(object);
                self.write(&format!("->{{{}}}", field.name));
            }
            ExprKind::Call { func, args } => {
                // Check for Reader/Writer constructor calls
                if let ExprKind::Ident(ident) = &func.kind
                    && (ident.name == "Reader" || ident.name == "Writer")
                {
                    self.write(&format!("{}->new(", ident.name));
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
                        // Convert .len() to scalar(@{$arr})
                        self.write("scalar(@{");
                        self.generate_expr(object);
                        self.write("})");
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
                        self.write("do { ");
                        for field_info in &fields {
                            if let Some(read_method) = self.get_read_method_for_type(&field_info.ty)
                            {
                                self.write(&format!(
                                    "${}->{{{}}} = ",
                                    var_ident.name, field_info.name
                                ));
                                self.generate_expr(object);
                                self.write(&format!("->{}(); ", read_method));
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
                            self.write("do { ");
                            for field_info in &fields {
                                if let Some(write_method) =
                                    self.get_write_method_for_type(&field_info.ty)
                                {
                                    self.generate_expr(object);
                                    self.write(&format!(
                                        "->{}(${}->{{{}}}); ",
                                        write_method, var_ident.name, field_info.name
                                    ));
                                }
                            }
                            self.write("}");
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
                        self.write(&format!("->{}(", field.name));
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

                // For function calls, emit the function name WITHOUT the $ sigil.
                // In Perl, only variables get $; function calls are bare names.
                if let ExprKind::Ident(ident) = &func.kind {
                    self.write(&ident.name);
                } else {
                    self.generate_expr(func);
                }
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
                // Generate as array reference
                if elements.is_empty() {
                    self.write("[]");
                } else {
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
                // Generate: [(value) x count]
                self.write("[(");
                self.generate_expr(value);
                self.write(") x ");
                self.generate_expr(count);
                self.write("]");
            }
            ExprKind::Cast { expr: inner, ty } => {
                self.generate_cast(inner, ty);
            }
            ExprKind::Ref(inner) | ExprKind::MutRef(inner) => {
                // References in Perl: for arrays, take a reference; for scalars, pass through
                if is_array_like_expr(inner) {
                    // Already an array ref from our generation
                    self.generate_expr(inner);
                } else {
                    self.generate_expr(inner);
                }
            }
            ExprKind::Deref(inner) => {
                // Dereferences - pass through
                self.generate_expr(inner);
            }
            ExprKind::Range { .. } => {
                // Ranges shouldn't appear outside of for loops
                self.write("# range");
            }
            ExprKind::Paren(inner) => {
                self.write("(");
                self.generate_expr(inner);
                self.write(")");
            }
            ExprKind::StructLit { name: _, fields } => {
                // Generate as hash reference
                self.write("{ ");
                for (i, (field_name, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&format!("{} => ", field_name.name));
                    self.generate_expr(value);
                }
                self.write(" }");
            }
            ExprKind::Conditional {
                condition,
                then_expr,
                else_expr,
            } => {
                // Perl ternary: condition ? then : else
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
                // Generate: EnumName_VariantName() or EnumName_VariantName(args...)
                self.write(&format!("{}_{}", enum_name.name, variant_name.name));
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.generate_expr(arg);
                }
                self.write(")");
            }
            ExprKind::Match { expr, arms } => {
                // Generate match as a do block with if-elsif-else chain
                self.write("do { my $__match = ");
                self.generate_expr(expr);
                self.write("; ");
                for (i, arm) in arms.iter().enumerate() {
                    if i > 0 {
                        self.write(" els");
                    }
                    self.generate_pattern_match(&arm.pattern, "$__match");
                    self.write(" { ");
                    self.generate_expr(&arm.body);
                    self.write("; }");
                }
                self.write(" }");
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
                // Should be resolved by monomorphization - generate placeholder
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
                self.write("if (1)");
            }
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("if ({} == ", scrutinee));
                self.generate_expr(lit_expr);
                self.write(")");
            }
            PatternKind::Ident(_ident) => {
                // Binding pattern - always matches
                self.write("if (1)");
            }
            PatternKind::EnumVariant {
                enum_name: _,
                variant_name,
                bindings,
            } => {
                self.write(&format!(
                    "if ({}->{{tag}} eq '{}'",
                    scrutinee, variant_name.name
                ));
                if !bindings.is_empty() {
                    // Bindings would extract v0, v1, etc. - handled in body
                }
                self.write(")");
            }
            PatternKind::Tuple(_patterns) => {
                self.write("if (1)");
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
            PatternKind::Wildcard => self.write("1"),
            PatternKind::Literal(lit_expr) => {
                self.write(&format!("{} == ", scrutinee));
                self.generate_expr(lit_expr);
            }
            PatternKind::Ident(_) => self.write("1"),
            PatternKind::EnumVariant { variant_name, .. } => {
                self.write(&format!(
                    "{}->{{tag}} eq '{}'",
                    scrutinee, variant_name.name
                ));
            }
            PatternKind::Tuple(_) => self.write("1"),
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
                let is_little = endian == Endianness::Little;
                let native = p.to_native();

                // Check if source is a slice/array (byte conversion)
                if is_byte_sequence_expr(expr) {
                    let byte_count = match native {
                        PrimitiveType::U16 | PrimitiveType::I16 => 2,
                        PrimitiveType::U32 | PrimitiveType::I32 => 4,
                        PrimitiveType::U64 | PrimitiveType::I64 => 8,
                        PrimitiveType::U128 | PrimitiveType::I128 => 16,
                        _ => 4,
                    };
                    // Generate: do { my @__b = @{expr}; (shift accumulation) }
                    self.write("do { my $__b = ");
                    self.generate_expr(expr);
                    self.write("; my $__v = 0; ");
                    if is_little {
                        for i in (0..byte_count).rev() {
                            self.write(&format!("$__v = ($__v << 8) | ($__b->[{}] & 0xFF); ", i));
                        }
                    } else {
                        for i in 0..byte_count {
                            self.write(&format!("$__v = ($__v << 8) | ($__b->[{}] & 0xFF); ", i));
                        }
                    }
                    self.write("$__v; }");
                    return;
                }

                // Integer to different endian - just mask to the appropriate size
                match native {
                    PrimitiveType::U16 | PrimitiveType::I16 => {
                        self.write("((");
                        self.generate_expr(expr);
                        self.write(") & 0xFFFF)");
                    }
                    PrimitiveType::U64 | PrimitiveType::I64 => {
                        self.write("_u64(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                    _ => {
                        self.write("_u32(");
                        self.generate_expr(expr);
                        self.write(")");
                    }
                }
                return;
            }
        }

        // Check for integer to byte array cast
        if let TypeKind::Array { element, size } = &ty.kind
            && let TypeKind::Primitive(PrimitiveType::U8) = &element.kind
        {
            let (is_little, _bits) = self.get_expr_endianness_info(expr);
            let byte_count = *size as usize;
            self.write("do { my $__v = ");
            // If expr is itself a cast, unwrap to get the inner value
            if let ExprKind::Cast { expr: inner, .. } = &expr.kind {
                self.generate_expr(inner);
            } else {
                self.generate_expr(expr);
            }
            self.write(&format!("; my $__a = [(0) x {}]; ", byte_count));
            for i in 0..byte_count {
                let shift = if is_little {
                    i * 8
                } else {
                    (byte_count - 1 - i) * 8
                };
                self.write(&format!("$__a->[{}] = ($__v >> {}) & 0xFF; ", i, shift));
            }
            self.write("$__a; }");
            return;
        }

        // Standard casts - masking
        match &ty.kind {
            TypeKind::Primitive(p) => match p {
                PrimitiveType::U8 | PrimitiveType::I8 => {
                    self.write("_u8(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::U16 | PrimitiveType::I16 => {
                    self.write("((");
                    self.generate_expr(expr);
                    self.write(") & 0xFFFF)");
                }
                PrimitiveType::U32 | PrimitiveType::I32 => {
                    self.write("_u32(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::U64 | PrimitiveType::I64 => {
                    self.write("_u64(");
                    self.generate_expr(expr);
                    self.write(")");
                }
                PrimitiveType::U128 | PrimitiveType::I128 => {
                    // Perl can handle large integers with use bigint, but we'll just mask
                    self.write("((");
                    self.generate_expr(expr);
                    self.write(") & ((2**128) - 1))");
                }
                PrimitiveType::Bool => {
                    self.write("((");
                    self.generate_expr(expr);
                    self.write(") ? 1 : 0)");
                }
                _ => {
                    // Endian types that reach here (shouldn't normally)
                    self.generate_expr(expr);
                }
            },
            _ => {
                self.generate_expr(expr);
            }
        }
    }

    /// Get endianness info from an expression (is_little_endian, bits)
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

/// Check if an expression involves 64-bit or larger types
fn expr_uses_u64(expr: &Expr) -> bool {
    use crate::parser::{PrimitiveType, TypeKind};

    match &expr.kind {
        ExprKind::Cast { ty, .. } => {
            if let TypeKind::Primitive(p) = &ty.kind {
                let native = p.to_native();
                matches!(
                    native,
                    PrimitiveType::U64
                        | PrimitiveType::I64
                        | PrimitiveType::U128
                        | PrimitiveType::I128
                )
            } else {
                false
            }
        }
        ExprKind::Binary { left, right, .. } => expr_uses_u64(left) || expr_uses_u64(right),
        ExprKind::Unary { operand, .. } => expr_uses_u64(operand),
        ExprKind::Paren(inner) => expr_uses_u64(inner),
        ExprKind::Integer(n) => *n > 0xFFFFFFFF,
        _ => false,
    }
}

#[allow(dead_code)]
fn escape_perl_string(s: &str) -> String {
    let mut result = String::new();
    for c in s.chars() {
        match c {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '$' => result.push_str("\\$"),
            '@' => result.push_str("\\@"),
            _ => result.push(c),
        }
    }
    result
}

impl Default for PerlGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGenerator for PerlGenerator {
    fn generate(&mut self, ast: &AnalyzedAst) -> AlgocResult<String> {
        self.output.clear();
        self.struct_defs.clear();
        self.struct_methods.clear();

        // Pre-pass: collect struct field info and methods for read/write generation
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

        self.writeln("#!/usr/bin/perl");
        self.writeln("# Generated by AlgoC");
        self.writeln("# DO NOT EDIT - This file is auto-generated");
        self.writeln("");
        self.writeln("use strict;");
        self.writeln("use warnings;");
        self.writeln("no warnings 'portable';");
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
            self.writeln("# Test Runner");
            self.writeln("sub run_tests {");
            self.indent();
            self.writeln("my $__passed = 0;");
            self.writeln("my $__failed = 0;");
            self.writeln("");

            for name in &test_names {
                self.writeln(&format!("$__test_name = '{}';", name));
                self.writeln("$__test_failures = 0;");
                self.writeln("eval {");
                self.indent();
                self.writeln(&format!("test_{}();", name));
                self.writeln("if ($__test_failures == 0) {");
                self.indent();
                self.writeln(&format!("print \"PASS: {}\\n\";", name));
                self.writeln("$__passed++;");
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!("print \"FAIL: {}\\n\";", name));
                self.writeln("$__failed++;");
                self.dedent();
                self.writeln("}");
                self.dedent();
                self.writeln("};");
                self.writeln("if ($@) {");
                self.indent();
                self.writeln(&format!("print \"FAIL: {} - $@\\n\";", name));
                self.writeln("$__failed++;");
                self.dedent();
                self.writeln("}");
                self.writeln("");
            }

            self.writeln("print \"\\n\";");
            self.writeln("print \"$__passed passed, $__failed failed\\n\";");
            self.writeln("return $__failed == 0 ? 1 : 0;");
            self.dedent();
            self.writeln("}");
            self.writeln("");

            // Auto-run tests
            self.writeln("# Auto-run tests");
            self.writeln("exit(run_tests() ? 0 : 1);");
        }

        Ok(self.output.clone())
    }

    fn file_extension(&self) -> &'static str {
        "pl"
    }

    fn language_name(&self) -> &'static str {
        "Perl"
    }
}
