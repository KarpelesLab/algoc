//! Type representation for semantic analysis
//!
//! These types are used during type checking and are separate from the AST types.

use std::fmt;

/// Endianness of an integer type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endianness {
    /// Native/system endianness (default)
    Native,
    /// Big endian (network byte order)
    Big,
    /// Little endian
    Little,
}

impl Endianness {
    /// Check if this is a specific (non-native) endianness
    pub fn is_specific(&self) -> bool {
        !matches!(self, Endianness::Native)
    }
}

/// A resolved type
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub kind: TypeKind,
}

impl Type {
    pub fn new(kind: TypeKind) -> Self {
        Self { kind }
    }

    /// Create an integer type with native endianness
    pub fn int(bits: u32, signed: bool) -> Self {
        Self::new(TypeKind::Int { bits, signed, endian: Endianness::Native })
    }

    /// Create an integer type with specific endianness
    pub fn int_endian(bits: u32, signed: bool, endian: Endianness) -> Self {
        Self::new(TypeKind::Int { bits, signed, endian })
    }

    /// Create a boolean type
    pub fn bool() -> Self {
        Self::new(TypeKind::Bool)
    }

    /// Create a unit type (void)
    pub fn unit() -> Self {
        Self::new(TypeKind::Unit)
    }

    /// Create an array type
    pub fn array(element: Type, size: u64) -> Self {
        Self::new(TypeKind::Array {
            element: Box::new(element),
            size,
        })
    }

    /// Create a slice type
    pub fn slice(element: Type) -> Self {
        Self::new(TypeKind::Slice {
            element: Box::new(element),
        })
    }

    /// Create a reference type
    pub fn reference(inner: Type, mutable: bool) -> Self {
        Self::new(TypeKind::Ref {
            inner: Box::new(inner),
            mutable,
        })
    }

    /// Create a struct type
    pub fn struct_type(name: String) -> Self {
        Self::new(TypeKind::Struct { name })
    }

    /// Create an error/unknown type (for error recovery)
    pub fn error() -> Self {
        Self::new(TypeKind::Error)
    }

    /// Create a Reader type
    pub fn reader() -> Self {
        Self::new(TypeKind::Reader)
    }

    /// Create a Writer type
    pub fn writer() -> Self {
        Self::new(TypeKind::Writer)
    }

    /// Check if this is an integer type
    pub fn is_integer(&self) -> bool {
        matches!(self.kind, TypeKind::Int { .. })
    }

    /// Check if this is a boolean type
    pub fn is_bool(&self) -> bool {
        matches!(self.kind, TypeKind::Bool)
    }

    /// Check if this is a reference type
    pub fn is_ref(&self) -> bool {
        matches!(self.kind, TypeKind::Ref { .. })
    }

    /// Check if this is a mutable reference
    pub fn is_mut_ref(&self) -> bool {
        matches!(self.kind, TypeKind::Ref { mutable: true, .. })
    }

    /// Check if this is an array type
    pub fn is_array(&self) -> bool {
        matches!(self.kind, TypeKind::Array { .. })
    }

    /// Check if this is a slice type
    pub fn is_slice(&self) -> bool {
        matches!(self.kind, TypeKind::Slice { .. })
    }

    /// Check if this is an error type
    pub fn is_error(&self) -> bool {
        matches!(self.kind, TypeKind::Error)
    }

    /// Check if this is a Reader type
    pub fn is_reader(&self) -> bool {
        matches!(self.kind, TypeKind::Reader)
    }

    /// Check if this is a Writer type
    pub fn is_writer(&self) -> bool {
        matches!(self.kind, TypeKind::Writer)
    }

    /// Get the element type if this is an array, slice, or reference to array/slice
    pub fn element_type(&self) -> Option<&Type> {
        match &self.kind {
            TypeKind::Array { element, .. } => Some(element),
            TypeKind::Slice { element } => Some(element),
            // References to arrays/slices can also be indexed
            TypeKind::Ref { inner, .. } => inner.element_type(),
            _ => None,
        }
    }

    /// Get the inner type if this is a reference
    pub fn deref_type(&self) -> Option<&Type> {
        match &self.kind {
            TypeKind::Ref { inner, .. } => Some(inner),
            _ => None,
        }
    }

    /// Get the bit width if this is an integer type
    pub fn bit_width(&self) -> Option<u32> {
        match &self.kind {
            TypeKind::Int { bits, .. } => Some(*bits),
            TypeKind::Bool => Some(1),
            _ => None,
        }
    }

    /// Get the endianness if this is an integer type
    pub fn endianness(&self) -> Option<Endianness> {
        match &self.kind {
            TypeKind::Int { endian, .. } => Some(*endian),
            _ => None,
        }
    }

    /// Check if this integer type has specific (non-native) endianness
    pub fn has_specific_endian(&self) -> bool {
        matches!(&self.kind, TypeKind::Int { endian, .. } if endian.is_specific())
    }

    /// Get the native version of this type (strip endianness)
    pub fn to_native_endian(&self) -> Type {
        match &self.kind {
            TypeKind::Int { bits, signed, .. } => Type::int(*bits, *signed),
            _ => self.clone(),
        }
    }

    /// Check if this type is assignable to another type
    pub fn is_assignable_to(&self, other: &Type) -> bool {
        if self.is_error() || other.is_error() {
            return true; // Error types are compatible with everything (for error recovery)
        }

        // Exact match
        if self == other {
            return true;
        }

        // Integer widening: smaller integers can be assigned to larger ones of same signedness
        // Also allow unsigned to unsigned and signed to signed regardless of size for literals
        // Different endianness is allowed (implicit conversion will be generated)
        match (&self.kind, &other.kind) {
            (TypeKind::Int { bits: from_bits, signed: from_signed, .. },
             TypeKind::Int { bits: to_bits, signed: to_signed, .. }) => {
                // Same size and signedness with different endianness is ok
                if from_bits == to_bits && from_signed == to_signed {
                    return true;
                }
                // Allow widening (small to large) with same signedness
                if from_signed == to_signed && from_bits <= to_bits {
                    return true;
                }
                // Allow unsigned literals to fit in larger unsigned types
                if !from_signed && !to_signed {
                    return true;
                }
                false
            }
            // Allow slice to be assigned where reference to fixed-size array is expected
            // (runtime bounds checking will be done in generated code)
            (TypeKind::Slice { element: from_elem },
             TypeKind::Ref { inner, mutable: false }) => {
                if let TypeKind::Array { element: to_elem, .. } = &inner.kind {
                    from_elem.is_assignable_to(to_elem)
                } else {
                    false
                }
            }
            // Allow &[T; N] to be passed where &[T] (slice) is expected
            (TypeKind::Ref { inner, mutable: _ },
             TypeKind::Slice { element: to_elem }) => {
                if let TypeKind::Array { element: from_elem, .. } = &inner.kind {
                    from_elem.is_assignable_to(to_elem)
                } else {
                    false
                }
            }
            // Allow &[T] (reference to slice) to be passed as &[T; N]
            (TypeKind::Ref { inner: from_inner, mutable: from_mut },
             TypeKind::Ref { inner: to_inner, mutable: to_mut }) => {
                // Mutability: &T can become &T, &mut T can become &T or &mut T
                if *to_mut && !from_mut {
                    return false; // Can't convert immutable to mutable
                }
                // Check if from is slice and to is array with compatible element types
                if let TypeKind::Slice { element: from_elem } = &from_inner.kind {
                    if let TypeKind::Array { element: to_elem, .. } = &to_inner.kind {
                        return from_elem.is_assignable_to(to_elem);
                    }
                }
                from_inner.is_assignable_to(to_inner)
            }
            // Allow arrays and slices with compatible element types to be compared
            (TypeKind::Array { element: arr_elem, .. }, TypeKind::Slice { element: slice_elem }) |
            (TypeKind::Slice { element: slice_elem }, TypeKind::Array { element: arr_elem, .. }) => {
                arr_elem.is_assignable_to(slice_elem) || slice_elem.is_assignable_to(arr_elem)
            }
            _ => false,
        }
    }

    /// Check if a value of this type can be used where `other` is expected
    pub fn is_compatible_with(&self, other: &Type) -> bool {
        self.is_assignable_to(other)
    }
}

/// The kind of a type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeKind {
    /// Integer type with bit width, signedness, and endianness
    Int { bits: u32, signed: bool, endian: Endianness },
    /// Boolean type
    Bool,
    /// Unit type (void, no value)
    Unit,
    /// Fixed-size array
    Array { element: Box<Type>, size: u64 },
    /// Slice (dynamically-sized view into array)
    Slice { element: Box<Type> },
    /// Reference (immutable or mutable)
    Ref { inner: Box<Type>, mutable: bool },
    /// Struct type (identified by name)
    Struct { name: String },
    /// Enum type (identified by name)
    Enum { name: String },
    /// Reader type (byte stream for reading)
    Reader,
    /// Writer type (byte stream for writing)
    Writer,
    /// Function type
    Function {
        params: Vec<Type>,
        return_type: Box<Type>,
    },
    /// Error type (used for error recovery)
    Error,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            TypeKind::Int { bits, signed, endian } => {
                let prefix = if *signed { "i" } else { "u" };
                let suffix = match endian {
                    Endianness::Native => "",
                    Endianness::Big => "be",
                    Endianness::Little => "le",
                };
                write!(f, "{}{}{}", prefix, bits, suffix)
            }
            TypeKind::Bool => write!(f, "bool"),
            TypeKind::Unit => write!(f, "()"),
            TypeKind::Array { element, size } => write!(f, "{}[{}]", element, size),
            TypeKind::Slice { element } => write!(f, "[{}]", element),
            TypeKind::Ref { inner, mutable } => {
                // Special case: reference to slice should display as &[T] or &mut [T]
                if let TypeKind::Slice { element } = &inner.kind {
                    if *mutable {
                        write!(f, "&mut [{}]", element)
                    } else {
                        write!(f, "&[{}]", element)
                    }
                } else if *mutable {
                    write!(f, "&mut {}", inner)
                } else {
                    write!(f, "&{}", inner)
                }
            }
            TypeKind::Struct { name } => write!(f, "{}", name),
            TypeKind::Enum { name } => write!(f, "{}", name),
            TypeKind::Reader => write!(f, "Reader"),
            TypeKind::Writer => write!(f, "Writer"),
            TypeKind::Function { params, return_type } => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, ") -> {}", return_type)
            }
            TypeKind::Error => write!(f, "<error>"),
        }
    }
}

/// A type error
#[derive(Debug, Clone)]
pub struct TypeError {
    pub message: String,
    pub expected: Option<Type>,
    pub found: Option<Type>,
}

impl TypeError {
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
            expected: None,
            found: None,
        }
    }

    pub fn mismatch(expected: Type, found: Type) -> Self {
        Self {
            message: format!("type mismatch: expected {}, found {}", expected, found),
            expected: Some(expected),
            found: Some(found),
        }
    }

    pub fn with_expected(mut self, ty: Type) -> Self {
        self.expected = Some(ty);
        self
    }

    pub fn with_found(mut self, ty: Type) -> Self {
        self.found = Some(ty);
        self
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

/// Predefined types for convenience
pub mod primitives {
    use super::*;

    pub fn u8() -> Type {
        Type::int(8, false)
    }
    pub fn u16() -> Type {
        Type::int(16, false)
    }
    pub fn u32() -> Type {
        Type::int(32, false)
    }
    pub fn u64() -> Type {
        Type::int(64, false)
    }
    pub fn u128() -> Type {
        Type::int(128, false)
    }
    pub fn i8() -> Type {
        Type::int(8, true)
    }
    pub fn i16() -> Type {
        Type::int(16, true)
    }
    pub fn i32() -> Type {
        Type::int(32, true)
    }
    pub fn i64() -> Type {
        Type::int(64, true)
    }
    pub fn i128() -> Type {
        Type::int(128, true)
    }
    pub fn bool() -> Type {
        Type::bool()
    }
}
