//! Hand-written lexer/scanner for AlgoC
//!
//! Converts source code into a stream of tokens.

use super::token::{Keyword, Token, TokenKind};
use crate::errors::SourceSpan;

/// The lexer/scanner for AlgoC source code
pub struct Lexer<'src> {
    /// The source code being lexed
    source: &'src str,
    /// Current byte position in the source
    pos: usize,
    /// Start position of the current token
    start: usize,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer for the given source code
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            pos: 0,
            start: 0,
        }
    }

    /// Get the current byte position
    pub fn position(&self) -> usize {
        self.pos
    }

    /// Peek at the current character without consuming it
    fn peek(&self) -> Option<char> {
        self.source[self.pos..].chars().next()
    }

    /// Peek at the next character (one ahead of current)
    fn peek_next(&self) -> Option<char> {
        let mut chars = self.source[self.pos..].chars();
        chars.next();
        chars.next()
    }

    /// Advance to the next character and return it
    fn advance(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    /// Check if we've reached the end of the source
    fn is_at_end(&self) -> bool {
        self.pos >= self.source.len()
    }

    /// Get the current span (from start to current position)
    fn current_span(&self) -> SourceSpan {
        SourceSpan::new(self.start, self.pos)
    }

    /// Get the current lexeme (text from start to current position)
    fn current_lexeme(&self) -> &'src str {
        &self.source[self.start..self.pos]
    }

    /// Create a token with the current span
    fn make_token(&self, kind: TokenKind) -> Token {
        Token::new(kind, self.current_span())
    }

    /// Consume the character if it matches the expected one
    fn match_char(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Skip whitespace and comments
    fn skip_whitespace(&mut self) {
        loop {
            match self.peek() {
                Some(' ' | '\t' | '\r' | '\n') => {
                    self.advance();
                }
                Some('/') if self.peek_next() == Some('/') => {
                    // Line comment
                    while self.peek().is_some_and(|c| c != '\n') {
                        self.advance();
                    }
                }
                Some('/') if self.peek_next() == Some('*') => {
                    // Block comment
                    self.advance(); // consume '/'
                    self.advance(); // consume '*'
                    let mut depth = 1;
                    while depth > 0 && !self.is_at_end() {
                        if self.peek() == Some('/') && self.peek_next() == Some('*') {
                            self.advance();
                            self.advance();
                            depth += 1;
                        } else if self.peek() == Some('*') && self.peek_next() == Some('/') {
                            self.advance();
                            self.advance();
                            depth -= 1;
                        } else {
                            self.advance();
                        }
                    }
                }
                _ => break,
            }
        }
    }

    /// Scan a number literal (decimal, hex, binary, or octal)
    fn scan_number(&mut self) -> Token {
        // Check for hex, binary, or octal prefix
        if self.current_lexeme() == "0" {
            match self.peek() {
                Some('x' | 'X') => {
                    self.advance();
                    return self.scan_hex_number();
                }
                Some('b' | 'B') => {
                    self.advance();
                    return self.scan_binary_number();
                }
                Some('o' | 'O') => {
                    self.advance();
                    return self.scan_octal_number();
                }
                _ => {}
            }
        }

        // Decimal number
        while self.peek().is_some_and(|c| c.is_ascii_digit() || c == '_') {
            self.advance();
        }

        let text = self.current_lexeme().replace('_', "");
        match text.parse::<u128>() {
            Ok(n) => self.make_token(TokenKind::Integer(n)),
            Err(_) => self.make_token(TokenKind::Error("number too large".to_string())),
        }
    }

    fn scan_hex_number(&mut self) -> Token {
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_hexdigit() || c == '_')
        {
            self.advance();
        }

        let text = &self.current_lexeme()[2..]; // skip "0x"
        let text = text.replace('_', "");
        match u128::from_str_radix(&text, 16) {
            Ok(n) => self.make_token(TokenKind::Integer(n)),
            Err(_) => self.make_token(TokenKind::Error("invalid hex number".to_string())),
        }
    }

    fn scan_binary_number(&mut self) -> Token {
        while self
            .peek()
            .is_some_and(|c| c == '0' || c == '1' || c == '_')
        {
            self.advance();
        }

        let text = &self.current_lexeme()[2..]; // skip "0b"
        let text = text.replace('_', "");
        match u128::from_str_radix(&text, 2) {
            Ok(n) => self.make_token(TokenKind::Integer(n)),
            Err(_) => self.make_token(TokenKind::Error("invalid binary number".to_string())),
        }
    }

    fn scan_octal_number(&mut self) -> Token {
        while self.peek().is_some_and(|c| matches!(c, '0'..='7' | '_')) {
            self.advance();
        }

        let text = &self.current_lexeme()[2..]; // skip "0o"
        let text = text.replace('_', "");
        match u128::from_str_radix(&text, 8) {
            Ok(n) => self.make_token(TokenKind::Integer(n)),
            Err(_) => self.make_token(TokenKind::Error("invalid octal number".to_string())),
        }
    }

    /// Scan a string literal
    fn scan_string(&mut self) -> Token {
        let mut value = String::new();

        while let Some(c) = self.peek() {
            if c == '"' {
                self.advance();
                return self.make_token(TokenKind::String(value));
            }

            self.advance();

            if c == '\\' {
                // Escape sequence
                match self.peek() {
                    Some('n') => {
                        value.push('\n');
                        self.advance();
                    }
                    Some('r') => {
                        value.push('\r');
                        self.advance();
                    }
                    Some('t') => {
                        value.push('\t');
                        self.advance();
                    }
                    Some('\\') => {
                        value.push('\\');
                        self.advance();
                    }
                    Some('"') => {
                        value.push('"');
                        self.advance();
                    }
                    Some('0') => {
                        value.push('\0');
                        self.advance();
                    }
                    Some('x') => {
                        self.advance();
                        // Hex escape: \xNN
                        let mut hex = String::new();
                        for _ in 0..2 {
                            if let Some(h) = self.peek()
                                && h.is_ascii_hexdigit()
                            {
                                hex.push(h);
                                self.advance();
                            }
                        }
                        if hex.len() == 2
                            && let Ok(byte) = u8::from_str_radix(&hex, 16)
                        {
                            value.push(byte as char);
                        }
                    }
                    _ => {
                        return self
                            .make_token(TokenKind::Error("invalid escape sequence".to_string()));
                    }
                }
            } else if c == '\n' {
                return self.make_token(TokenKind::Error(
                    "unterminated string (newline in string)".to_string(),
                ));
            } else {
                value.push(c);
            }
        }

        self.make_token(TokenKind::Error("unterminated string".to_string()))
    }

    /// Scan an identifier or keyword
    fn scan_identifier(&mut self) -> Token {
        while self
            .peek()
            .is_some_and(|c| c.is_ascii_alphanumeric() || c == '_')
        {
            self.advance();
        }

        let text = self.current_lexeme();

        // Check if it's a keyword
        if let Some(kw) = Keyword::parse(text) {
            self.make_token(TokenKind::Keyword(kw))
        } else {
            self.make_token(TokenKind::Ident(text.to_string()))
        }
    }

    /// Scan the next token
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();
        self.start = self.pos;

        if self.is_at_end() {
            return self.make_token(TokenKind::Eof);
        }

        let c = self.advance().unwrap();

        // Identifiers and keywords
        if c.is_ascii_alphabetic() || c == '_' {
            return self.scan_identifier();
        }

        // Numbers
        if c.is_ascii_digit() {
            return self.scan_number();
        }

        // String literals
        if c == '"' {
            return self.scan_string();
        }

        // Punctuation and operators
        match c {
            '(' => self.make_token(TokenKind::LParen),
            ')' => self.make_token(TokenKind::RParen),
            '{' => self.make_token(TokenKind::LBrace),
            '}' => self.make_token(TokenKind::RBrace),
            '[' => self.make_token(TokenKind::LBracket),
            ']' => self.make_token(TokenKind::RBracket),
            ';' => self.make_token(TokenKind::Semicolon),
            ':' => {
                if self.match_char(':') {
                    self.make_token(TokenKind::ColonColon)
                } else {
                    self.make_token(TokenKind::Colon)
                }
            }
            ',' => self.make_token(TokenKind::Comma),
            '@' => self.make_token(TokenKind::At),
            '~' => self.make_token(TokenKind::Tilde),

            '.' => {
                if self.match_char('.') {
                    if self.match_char('=') {
                        self.make_token(TokenKind::DotDotEq)
                    } else {
                        self.make_token(TokenKind::DotDot)
                    }
                } else {
                    self.make_token(TokenKind::Dot)
                }
            }

            '+' => {
                if self.match_char('=') {
                    self.make_token(TokenKind::PlusEq)
                } else {
                    self.make_token(TokenKind::Plus)
                }
            }

            '-' => {
                if self.match_char('=') {
                    self.make_token(TokenKind::MinusEq)
                } else if self.match_char('>') {
                    self.make_token(TokenKind::Arrow)
                } else {
                    self.make_token(TokenKind::Minus)
                }
            }

            '*' => {
                if self.match_char('=') {
                    self.make_token(TokenKind::StarEq)
                } else {
                    self.make_token(TokenKind::Star)
                }
            }

            '/' => {
                if self.match_char('=') {
                    self.make_token(TokenKind::SlashEq)
                } else {
                    self.make_token(TokenKind::Slash)
                }
            }

            '%' => {
                if self.match_char('=') {
                    self.make_token(TokenKind::PercentEq)
                } else {
                    self.make_token(TokenKind::Percent)
                }
            }

            '&' => {
                if self.match_char('&') {
                    self.make_token(TokenKind::AmpAmp)
                } else if self.match_char('=') {
                    self.make_token(TokenKind::AmpEq)
                } else {
                    self.make_token(TokenKind::Amp)
                }
            }

            '|' => {
                if self.match_char('|') {
                    self.make_token(TokenKind::PipePipe)
                } else if self.match_char('=') {
                    self.make_token(TokenKind::PipeEq)
                } else {
                    self.make_token(TokenKind::Pipe)
                }
            }

            '^' => {
                if self.match_char('=') {
                    self.make_token(TokenKind::CaretEq)
                } else {
                    self.make_token(TokenKind::Caret)
                }
            }

            '!' => {
                if self.match_char('=') {
                    self.make_token(TokenKind::BangEq)
                } else {
                    self.make_token(TokenKind::Bang)
                }
            }

            '=' => {
                if self.match_char('=') {
                    self.make_token(TokenKind::EqEq)
                } else if self.match_char('>') {
                    self.make_token(TokenKind::FatArrow)
                } else {
                    self.make_token(TokenKind::Eq)
                }
            }

            '<' => {
                if self.match_char('<') {
                    if self.match_char('=') {
                        self.make_token(TokenKind::LtLtEq)
                    } else {
                        self.make_token(TokenKind::LtLt)
                    }
                } else if self.match_char('=') {
                    self.make_token(TokenKind::LtEq)
                } else {
                    self.make_token(TokenKind::Lt)
                }
            }

            '>' => {
                if self.match_char('>') {
                    if self.match_char('=') {
                        self.make_token(TokenKind::GtGtEq)
                    } else {
                        self.make_token(TokenKind::GtGt)
                    }
                } else if self.match_char('=') {
                    self.make_token(TokenKind::GtEq)
                } else {
                    self.make_token(TokenKind::Gt)
                }
            }

            _ => self.make_token(TokenKind::Error(format!("unexpected character: {}", c))),
        }
    }

    /// Collect all tokens into a vector
    pub fn tokenize(mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let token = self.next_token();
            let is_eof = token.kind.is_eof();
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        tokens
    }
}

impl<'src> Iterator for Lexer<'src> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.next_token();
        if token.kind.is_eof() {
            None
        } else {
            Some(token)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(source: &str) -> Vec<TokenKind> {
        Lexer::new(source)
            .tokenize()
            .into_iter()
            .map(|t| t.kind)
            .collect()
    }

    #[test]
    fn test_basic_tokens() {
        let tokens = lex("( ) { } [ ] ; : , . @");
        assert_eq!(
            tokens,
            vec![
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::LBrace,
                TokenKind::RBrace,
                TokenKind::LBracket,
                TokenKind::RBracket,
                TokenKind::Semicolon,
                TokenKind::Colon,
                TokenKind::Comma,
                TokenKind::Dot,
                TokenKind::At,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_operators() {
        let tokens = lex("+ - * / % & | ^ ~ !");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Star,
                TokenKind::Slash,
                TokenKind::Percent,
                TokenKind::Amp,
                TokenKind::Pipe,
                TokenKind::Caret,
                TokenKind::Tilde,
                TokenKind::Bang,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_compound_operators() {
        let tokens = lex("== != <= >= << >> && || += -= -> ..");
        assert_eq!(
            tokens,
            vec![
                TokenKind::EqEq,
                TokenKind::BangEq,
                TokenKind::LtEq,
                TokenKind::GtEq,
                TokenKind::LtLt,
                TokenKind::GtGt,
                TokenKind::AmpAmp,
                TokenKind::PipePipe,
                TokenKind::PlusEq,
                TokenKind::MinusEq,
                TokenKind::Arrow,
                TokenKind::DotDot,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_numbers() {
        let tokens = lex("42 0x1F 0b1010 0o77 1_000_000");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Integer(42),
                TokenKind::Integer(0x1F),
                TokenKind::Integer(0b1010),
                TokenKind::Integer(0o77),
                TokenKind::Integer(1_000_000),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_strings() {
        let tokens = lex(r#""hello" "world\n" "tab\there""#);
        assert_eq!(
            tokens,
            vec![
                TokenKind::String("hello".to_string()),
                TokenKind::String("world\n".to_string()),
                TokenKind::String("tab\there".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_keywords() {
        let tokens = lex("fn struct const let if else for while return");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Keyword(Keyword::Fn),
                TokenKind::Keyword(Keyword::Struct),
                TokenKind::Keyword(Keyword::Const),
                TokenKind::Keyword(Keyword::Let),
                TokenKind::Keyword(Keyword::If),
                TokenKind::Keyword(Keyword::Else),
                TokenKind::Keyword(Keyword::For),
                TokenKind::Keyword(Keyword::While),
                TokenKind::Keyword(Keyword::Return),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_type_keywords() {
        let tokens = lex("u8 u16 u32 u64 u128 i8 i16 i32 i64 i128 bool");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Keyword(Keyword::U8),
                TokenKind::Keyword(Keyword::U16),
                TokenKind::Keyword(Keyword::U32),
                TokenKind::Keyword(Keyword::U64),
                TokenKind::Keyword(Keyword::U128),
                TokenKind::Keyword(Keyword::I8),
                TokenKind::Keyword(Keyword::I16),
                TokenKind::Keyword(Keyword::I32),
                TokenKind::Keyword(Keyword::I64),
                TokenKind::Keyword(Keyword::I128),
                TokenKind::Keyword(Keyword::Bool),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        let tokens = lex("foo bar_baz _private MyStruct");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Ident("foo".to_string()),
                TokenKind::Ident("bar_baz".to_string()),
                TokenKind::Ident("_private".to_string()),
                TokenKind::Ident("MyStruct".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_comments() {
        let tokens = lex("a // line comment\nb /* block */ c");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Ident("a".to_string()),
                TokenKind::Ident("b".to_string()),
                TokenKind::Ident("c".to_string()),
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_sample_code() {
        let tokens = lex(r#"
            fn compress(state: &mut State, block: &[u8; 64]) {
                let w: u32[64];
                for i in 0..16 {
                    w[i] = read_u32_be(block, i * 4);
                }
            }
            "#);

        // Just verify it doesn't crash and produces expected structure
        assert!(tokens.len() > 20);
        assert!(matches!(tokens.last(), Some(TokenKind::Eof)));
    }
}
