//! Abstract Syntax Tree (AST) definitions for AlgoC
//!
//! These types represent the structure of an AlgoC program after parsing.

use crate::errors::SourceSpan;

/// A complete AlgoC program/module
#[derive(Debug, Clone)]
pub struct Ast {
    /// All items in the module
    pub items: Vec<Item>,
}

/// A top-level item in a module
#[derive(Debug, Clone)]
pub struct Item {
    pub kind: ItemKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    /// Use/import declaration: `use "path/to/file.algoc";`
    Use(UseDef),
    /// Function definition: `fn name(params) -> RetType { body }`
    Function(Function),
    /// Struct definition: `struct Name { fields }`
    Struct(StructDef),
    /// Layout definition: `layout Name { fields }`
    Layout(LayoutDef),
    /// Constant definition: `const NAME: Type = value;`
    Const(ConstDef),
    /// Enum definition: `enum Name { Variant1, Variant2(T), ... }`
    Enum(EnumDef),
    /// Impl block: `impl StructName { fn method(&self) { ... } }`
    Impl(ImplDef),
    /// Test definition: `test name { input: ..., expect: ... }`
    Test(TestDef),
}

/// A use/import declaration
#[derive(Debug, Clone)]
pub struct UseDef {
    pub path: String,
    pub span: SourceSpan,
}

/// A function definition
#[derive(Debug, Clone)]
pub struct Function {
    pub name: Ident,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    pub body: Block,
}

/// A function parameter
#[derive(Debug, Clone)]
pub struct Param {
    pub name: Ident,
    pub ty: Type,
    pub span: SourceSpan,
}

/// A struct definition
#[derive(Debug, Clone)]
pub struct StructDef {
    pub name: Ident,
    pub fields: Vec<Field>,
}

/// A struct field
#[derive(Debug, Clone)]
pub struct Field {
    pub name: Ident,
    pub ty: Type,
    pub modifiers: Vec<TypeModifier>,
    pub span: SourceSpan,
}

/// A layout definition (for bit-level access)
#[derive(Debug, Clone)]
pub struct LayoutDef {
    pub name: Ident,
    pub fields: Vec<LayoutField>,
}

/// A layout field with bit range
#[derive(Debug, Clone)]
pub struct LayoutField {
    pub bits_start: u64,
    pub bits_end: u64,
    pub name: Ident,
    pub ty: Type,
    pub span: SourceSpan,
}

/// A constant definition
#[derive(Debug, Clone)]
pub struct ConstDef {
    pub name: Ident,
    pub ty: Type,
    pub value: Expr,
}

/// An enum definition
#[derive(Debug, Clone)]
pub struct EnumDef {
    pub name: Ident,
    pub variants: Vec<EnumVariant>,
}

/// An enum variant
#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: Ident,
    pub data: EnumVariantData,
    pub span: SourceSpan,
}

/// Data associated with an enum variant
#[derive(Debug, Clone)]
pub enum EnumVariantData {
    /// Unit variant: `Red`
    Unit,
    /// Tuple variant: `Rgb(u8, u8, u8)`
    Tuple(Vec<Type>),
    /// Struct variant: `Point { x: i32, y: i32 }`
    Struct(Vec<Field>),
}

/// An impl block definition
#[derive(Debug, Clone)]
pub struct ImplDef {
    /// The type this impl is for
    pub target: Ident,
    /// Methods defined in this impl block
    pub methods: Vec<Function>,
    pub span: SourceSpan,
}

/// A test definition (function-like)
#[derive(Debug, Clone)]
pub struct TestDef {
    pub name: Ident,
    pub body: Block,
    pub span: SourceSpan,
}

/// An identifier with source location
#[derive(Debug, Clone)]
pub struct Ident {
    pub name: String,
    pub span: SourceSpan,
}

impl Ident {
    pub fn new(name: impl Into<String>, span: SourceSpan) -> Self {
        Self {
            name: name.into(),
            span,
        }
    }
}

/// A type expression
#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    /// Primitive type: u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, bool
    Primitive(PrimitiveType),
    /// Array type: T[N]
    Array {
        element: Box<Type>,
        size: u64,
    },
    /// Slice type: &[T]
    Slice {
        element: Box<Type>,
    },
    /// Reference to fixed array: &[T; N]
    ArrayRef {
        element: Box<Type>,
        size: u64,
    },
    /// Mutable reference: &mut T
    MutRef(Box<Type>),
    /// Immutable reference: &T
    Ref(Box<Type>),
    /// Named type (struct or type alias)
    Named(Ident),
}

/// Endianness for primitive types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endianness {
    /// Native/system endianness (default)
    Native,
    /// Big endian (network byte order)
    Big,
    /// Little endian
    Little,
}

/// Primitive types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveType {
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    Bool,
    // Big-endian types
    U16Be,
    U32Be,
    U64Be,
    U128Be,
    I16Be,
    I32Be,
    I64Be,
    I128Be,
    // Little-endian types
    U16Le,
    U32Le,
    U64Le,
    U128Le,
    I16Le,
    I32Le,
    I64Le,
    I128Le,
}

impl PrimitiveType {
    /// Get the bit width of this type
    pub fn bit_width(&self) -> u32 {
        match self {
            PrimitiveType::U8 | PrimitiveType::I8 => 8,
            PrimitiveType::U16 | PrimitiveType::I16 |
            PrimitiveType::U16Be | PrimitiveType::I16Be |
            PrimitiveType::U16Le | PrimitiveType::I16Le => 16,
            PrimitiveType::U32 | PrimitiveType::I32 |
            PrimitiveType::U32Be | PrimitiveType::I32Be |
            PrimitiveType::U32Le | PrimitiveType::I32Le => 32,
            PrimitiveType::U64 | PrimitiveType::I64 |
            PrimitiveType::U64Be | PrimitiveType::I64Be |
            PrimitiveType::U64Le | PrimitiveType::I64Le => 64,
            PrimitiveType::U128 | PrimitiveType::I128 |
            PrimitiveType::U128Be | PrimitiveType::I128Be |
            PrimitiveType::U128Le | PrimitiveType::I128Le => 128,
            PrimitiveType::Bool => 1,
        }
    }

    /// Check if this is a signed type
    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            PrimitiveType::I8 | PrimitiveType::I16 | PrimitiveType::I32 |
            PrimitiveType::I64 | PrimitiveType::I128 |
            PrimitiveType::I16Be | PrimitiveType::I32Be |
            PrimitiveType::I64Be | PrimitiveType::I128Be |
            PrimitiveType::I16Le | PrimitiveType::I32Le |
            PrimitiveType::I64Le | PrimitiveType::I128Le
        )
    }

    /// Get the endianness of this type
    pub fn endianness(&self) -> Endianness {
        match self {
            PrimitiveType::U16Be | PrimitiveType::U32Be |
            PrimitiveType::U64Be | PrimitiveType::U128Be |
            PrimitiveType::I16Be | PrimitiveType::I32Be |
            PrimitiveType::I64Be | PrimitiveType::I128Be => Endianness::Big,
            PrimitiveType::U16Le | PrimitiveType::U32Le |
            PrimitiveType::U64Le | PrimitiveType::U128Le |
            PrimitiveType::I16Le | PrimitiveType::I32Le |
            PrimitiveType::I64Le | PrimitiveType::I128Le => Endianness::Little,
            _ => Endianness::Native,
        }
    }

    /// Get the native (no endianness) version of this type
    pub fn to_native(&self) -> PrimitiveType {
        match self {
            PrimitiveType::U16Be | PrimitiveType::U16Le => PrimitiveType::U16,
            PrimitiveType::U32Be | PrimitiveType::U32Le => PrimitiveType::U32,
            PrimitiveType::U64Be | PrimitiveType::U64Le => PrimitiveType::U64,
            PrimitiveType::U128Be | PrimitiveType::U128Le => PrimitiveType::U128,
            PrimitiveType::I16Be | PrimitiveType::I16Le => PrimitiveType::I16,
            PrimitiveType::I32Be | PrimitiveType::I32Le => PrimitiveType::I32,
            PrimitiveType::I64Be | PrimitiveType::I64Le => PrimitiveType::I64,
            PrimitiveType::I128Be | PrimitiveType::I128Le => PrimitiveType::I128,
            other => *other,
        }
    }
}

/// Type modifiers (attributes)
#[derive(Debug, Clone)]
pub struct TypeModifier {
    pub kind: TypeModifierKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum TypeModifierKind {
    BigEndian,
    LittleEndian,
    Aligned(u64),
    Packed,
}

/// A block of statements
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: SourceSpan,
}

/// A statement
#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    /// Variable declaration: `let name: Type = value;` or `let name: Type;`
    Let {
        name: Ident,
        ty: Option<Type>,
        mutable: bool,
        init: Option<Expr>,
    },
    /// Expression statement
    Expr(Expr),
    /// Assignment: `place = value;`
    Assign {
        target: Expr,
        value: Expr,
    },
    /// Compound assignment: `place += value;`
    CompoundAssign {
        target: Expr,
        op: BinaryOp,
        value: Expr,
    },
    /// If statement
    If {
        condition: Expr,
        then_block: Block,
        else_block: Option<Block>,
    },
    /// For loop: `for i in start..end { body }`
    For {
        var: Ident,
        start: Expr,
        end: Expr,
        inclusive: bool,
        body: Block,
    },
    /// While loop
    While {
        condition: Expr,
        body: Block,
    },
    /// Infinite loop
    Loop {
        body: Block,
    },
    /// Break
    Break,
    /// Continue
    Continue,
    /// Return
    Return(Option<Expr>),
    /// Block
    Block(Block),
}

/// An expression
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// Integer literal
    Integer(u128),
    /// Boolean literal
    Bool(bool),
    /// String literal
    String(String),
    /// Identifier
    Ident(Ident),
    /// Binary operation: `a + b`
    Binary {
        left: Box<Expr>,
        op: BinaryOp,
        right: Box<Expr>,
    },
    /// Unary operation: `-a`, `!a`, `~a`
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    /// Array indexing: `arr[idx]`
    Index {
        array: Box<Expr>,
        index: Box<Expr>,
    },
    /// Array/slice slicing: `arr[start..end]` or `arr[start..=end]`
    Slice {
        array: Box<Expr>,
        start: Box<Expr>,
        end: Box<Expr>,
        inclusive: bool,
    },
    /// Field access: `obj.field`
    Field {
        object: Box<Expr>,
        field: Ident,
    },
    /// Function call: `func(args)`
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    /// Built-in function call
    Builtin {
        name: BuiltinFunc,
        args: Vec<Expr>,
    },
    /// Array literal: `[1, 2, 3]`
    Array(Vec<Expr>),
    /// Array repeat: `[value; count]` - count can be a runtime expression
    ArrayRepeat {
        value: Box<Expr>,
        count: Box<Expr>,
    },
    /// Cast: `expr as Type`
    Cast {
        expr: Box<Expr>,
        ty: Type,
    },
    /// Reference: `&expr`
    Ref(Box<Expr>),
    /// Mutable reference: `&mut expr`
    MutRef(Box<Expr>),
    /// Dereference: `*expr`
    Deref(Box<Expr>),
    /// Range: `start..end` or `start..=end`
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        inclusive: bool,
    },
    /// Parenthesized expression
    Paren(Box<Expr>),
    /// Struct literal: `Name { field: value, ... }`
    StructLit {
        name: Ident,
        fields: Vec<(Ident, Expr)>,
    },
    /// Bytes literal: `bytes("hello")`
    Bytes(String),
    /// Hex literal: `hex("deadbeef")`
    Hex(String),
    /// Conditional expression: `then_value if condition else else_value`
    Conditional {
        condition: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    /// Enum variant construction: `Color::Red` or `Color::Rgb(1, 2, 3)`
    EnumVariant {
        enum_name: Ident,
        variant_name: Ident,
        args: Vec<Expr>,
    },
    /// Match expression: `match expr { pattern => result, ... }`
    Match {
        expr: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    /// Method call (added by type checker): `receiver.method(args)` -> resolved function name
    MethodCall {
        receiver: Box<Expr>,
        method_name: String,
        mangled_name: String,
        args: Vec<Expr>,
    },
}

/// A match arm: `pattern => expression`
#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub body: Expr,
    pub span: SourceSpan,
}

/// A pattern for matching
#[derive(Debug, Clone)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone)]
pub enum PatternKind {
    /// Wildcard pattern: `_`
    Wildcard,
    /// Literal pattern: `42`, `true`
    Literal(Expr),
    /// Identifier binding: `x`
    Ident(Ident),
    /// Enum variant pattern: `Color::Red` or `Color::Rgb(r, g, b)`
    EnumVariant {
        enum_name: Ident,
        variant_name: Ident,
        bindings: Vec<Pattern>,
    },
    /// Tuple pattern: `(a, b, c)`
    Tuple(Vec<Pattern>),
    /// Or pattern: `A | B`
    Or(Vec<Pattern>),
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Rem,

    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,

    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Logical
    And,
    Or,
}

impl BinaryOp {
    /// Get the precedence of this operator (higher = binds tighter)
    pub fn precedence(&self) -> u8 {
        match self {
            BinaryOp::Or => 1,
            BinaryOp::And => 2,
            BinaryOp::Eq | BinaryOp::Ne => 3,
            BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => 4,
            BinaryOp::BitOr => 5,
            BinaryOp::BitXor => 6,
            BinaryOp::BitAnd => 7,
            BinaryOp::Shl | BinaryOp::Shr => 8,
            BinaryOp::Add | BinaryOp::Sub => 9,
            BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem => 10,
        }
    }

    /// Check if this operator is right-associative
    pub fn is_right_assoc(&self) -> bool {
        false // All binary ops are left-associative
    }
}

/// Unary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,    // -
    Not,    // !
    BitNot, // ~
}

/// Built-in functions (compiler intrinsics)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinFunc {
    // Testing - compiler handles this specially
    Assert,
}
