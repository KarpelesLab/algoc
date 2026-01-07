//! Pretty error reporting using ariadne
//!
//! Provides colorful, user-friendly error messages with source context.

use ariadne::{Color, Label, Report, ReportKind, Source};
use crate::errors::AlgocError;

/// Print an error with source context
pub fn print_error(source: &str, filename: &str, error: &AlgocError) {
    let (message, span, kind) = match error {
        AlgocError::Lexer { message, span } => (message.as_str(), Some(*span), "Lexer error"),
        AlgocError::Parser { message, span } => (message.as_str(), Some(*span), "Parser error"),
        AlgocError::Type { message, span } => (message.as_str(), Some(*span), "Type error"),
        AlgocError::Semantic { message, span } => (message.as_str(), Some(*span), "Semantic error"),
        AlgocError::CodeGen { message, span } => (message.as_str(), *span, "Code generation error"),
        AlgocError::Io(e) => {
            eprintln!("IO error: {}", e);
            return;
        }
    };

    let span_range = span.map(|s| s.start..s.end).unwrap_or(0..0);

    let mut report = Report::build(ReportKind::Error, span_range.clone())
        .with_message(kind);

    if let Some(s) = span {
        report = report.with_label(
            Label::new(s.start..s.end)
                .with_message(message)
                .with_color(Color::Red),
        );
    }

    report
        .finish()
        .print(Source::from(source))
        .expect("failed to print error report");
}

/// Print multiple errors
pub fn print_errors(source: &str, _filename: &str, errors: &[AlgocError]) {
    for error in errors {
        print_error(source, "", error);
    }
}

/// Format an error as a string (for testing)
pub fn format_error(source: &str, _filename: &str, error: &AlgocError) -> String {
    let (message, span, kind) = match error {
        AlgocError::Lexer { message, span } => (message.as_str(), Some(*span), "Lexer error"),
        AlgocError::Parser { message, span } => (message.as_str(), Some(*span), "Parser error"),
        AlgocError::Type { message, span } => (message.as_str(), Some(*span), "Type error"),
        AlgocError::Semantic { message, span } => (message.as_str(), Some(*span), "Semantic error"),
        AlgocError::CodeGen { message, span } => (message.as_str(), *span, "Code generation error"),
        AlgocError::Io(e) => return format!("IO error: {}", e),
    };

    let mut output = Vec::new();
    let span_range = span.map(|s| s.start..s.end).unwrap_or(0..0);

    let mut report = Report::build(ReportKind::Error, span_range.clone())
        .with_message(kind);

    if let Some(s) = span {
        report = report.with_label(
            Label::new(s.start..s.end)
                .with_message(message)
                .with_color(Color::Red),
        );
    }

    report
        .finish()
        .write(Source::from(source), &mut output)
        .expect("failed to write error report");

    String::from_utf8(output).expect("error report should be valid UTF-8")
}

/// Get the line and column for a byte offset
pub fn offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;

    for (i, c) in source.char_indices() {
        if i >= offset {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }

    (line, col)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_offset_to_line_col() {
        let source = "line1\nline2\nline3";

        assert_eq!(offset_to_line_col(source, 0), (1, 1));
        assert_eq!(offset_to_line_col(source, 5), (1, 6));
        assert_eq!(offset_to_line_col(source, 6), (2, 1));
        assert_eq!(offset_to_line_col(source, 12), (3, 1));
    }
}
