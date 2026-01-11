//! Error handling for AlgoC
//!
//! Provides structured error types with source location tracking
//! for helpful diagnostic messages.

mod diagnostic;

use std::fmt;
use std::ops::Range;
use thiserror::Error;

pub use diagnostic::{format_error, print_error, print_errors};

/// A span in the source code, represented as a byte range
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceSpan {
    /// Start byte offset (inclusive)
    pub start: usize,
    /// End byte offset (exclusive)
    pub end: usize,
}

impl SourceSpan {
    /// Create a new source span
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Create a span from a range
    pub fn from_range(range: Range<usize>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }

    /// Merge two spans into one that covers both
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    /// Get the length of this span
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Check if the span is empty
    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }
}

impl From<Range<usize>> for SourceSpan {
    fn from(range: Range<usize>) -> Self {
        Self::from_range(range)
    }
}

impl From<SourceSpan> for Range<usize> {
    fn from(span: SourceSpan) -> Self {
        span.start..span.end
    }
}

/// The main error type for AlgoC operations
#[derive(Error, Debug)]
pub enum AlgocError {
    #[error("Lexer error: {message}")]
    Lexer { message: String, span: SourceSpan },

    #[error("Parser error: {message}")]
    Parser { message: String, span: SourceSpan },

    #[error("Type error: {message}")]
    Type { message: String, span: SourceSpan },

    #[error("Semantic error: {message}")]
    Semantic { message: String, span: SourceSpan },

    #[error("Code generation error: {message}")]
    CodeGen {
        message: String,
        span: Option<SourceSpan>,
    },

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

impl AlgocError {
    /// Get the source span associated with this error, if any
    pub fn span(&self) -> Option<SourceSpan> {
        match self {
            AlgocError::Lexer { span, .. } => Some(*span),
            AlgocError::Parser { span, .. } => Some(*span),
            AlgocError::Type { span, .. } => Some(*span),
            AlgocError::Semantic { span, .. } => Some(*span),
            AlgocError::CodeGen { span, .. } => *span,
            AlgocError::Io(_) => None,
        }
    }

    /// Create a lexer error
    pub fn lexer(message: impl Into<String>, span: SourceSpan) -> Self {
        AlgocError::Lexer {
            message: message.into(),
            span,
        }
    }

    /// Create a parser error
    pub fn parser(message: impl Into<String>, span: SourceSpan) -> Self {
        AlgocError::Parser {
            message: message.into(),
            span,
        }
    }

    /// Create a type error
    pub fn type_error(message: impl Into<String>, span: SourceSpan) -> Self {
        AlgocError::Type {
            message: message.into(),
            span,
        }
    }

    /// Create a semantic error
    pub fn semantic(message: impl Into<String>, span: SourceSpan) -> Self {
        AlgocError::Semantic {
            message: message.into(),
            span,
        }
    }
}

/// Result type alias for AlgoC operations
pub type AlgocResult<T> = Result<T, AlgocError>;

/// A located item wraps a value with its source span
#[derive(Debug, Clone)]
pub struct Located<T> {
    pub value: T,
    pub span: SourceSpan,
}

impl<T> Located<T> {
    pub fn new(value: T, span: SourceSpan) -> Self {
        Self { value, span }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Located<U> {
        Located {
            value: f(self.value),
            span: self.span,
        }
    }
}

impl<T: fmt::Display> fmt::Display for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
