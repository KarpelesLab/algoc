//! Recursive descent parser for AlgoC
//!
//! Parses a token stream into an AST.

use crate::errors::{AlgocError, AlgocResult, SourceSpan};
use crate::lexer::{Keyword, Lexer, Token, TokenKind};
use super::ast::*;

/// The parser for AlgoC source code
pub struct Parser<'src> {
    /// The source code (for error messages)
    source: &'src str,
    /// Tokens from the lexer
    tokens: Vec<Token>,
    /// Current position in the token stream
    pos: usize,
}

impl<'src> Parser<'src> {
    /// Create a new parser for the given source code
    pub fn new(source: &'src str) -> Self {
        let lexer = Lexer::new(source);
        let tokens = lexer.tokenize();
        Self {
            source,
            tokens,
            pos: 0,
        }
    }

    /// Parse the source code into an AST
    pub fn parse(mut self) -> AlgocResult<Ast> {
        let mut items = Vec::new();

        while !self.is_at_end() {
            items.push(self.parse_item()?);
        }

        Ok(Ast { items })
    }

    // ==================== Helpers ====================

    /// Check if we've reached EOF
    fn is_at_end(&self) -> bool {
        self.peek().kind.is_eof()
    }

    /// Peek at the current token
    fn peek(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or_else(|| {
            self.tokens.last().expect("tokens should have at least EOF")
        })
    }

    /// Peek at the next token (one ahead)
    fn peek_next(&self) -> &Token {
        self.tokens.get(self.pos + 1).unwrap_or_else(|| {
            self.tokens.last().expect("tokens should have at least EOF")
        })
    }

    /// Get the current token's span
    fn current_span(&self) -> SourceSpan {
        self.peek().span
    }

    /// Advance and return the previous token
    fn advance(&mut self) -> &Token {
        if !self.is_at_end() {
            self.pos += 1;
        }
        self.previous()
    }

    /// Get the previous token
    fn previous(&self) -> &Token {
        &self.tokens[self.pos.saturating_sub(1)]
    }

    /// Check if current token matches
    fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.peek().kind) == std::mem::discriminant(kind)
    }

    /// Check if current token is a keyword
    fn check_keyword(&self, kw: Keyword) -> bool {
        matches!(&self.peek().kind, TokenKind::Keyword(k) if *k == kw)
    }

    /// Consume a token if it matches, otherwise error
    fn expect(&mut self, kind: &TokenKind, msg: &str) -> AlgocResult<&Token> {
        if self.check(kind) {
            Ok(self.advance())
        } else {
            Err(AlgocError::parser(
                format!("{}, found {}", msg, self.peek().kind),
                self.current_span(),
            ))
        }
    }

    /// Consume a keyword if it matches, otherwise error
    fn expect_keyword(&mut self, kw: Keyword, msg: &str) -> AlgocResult<SourceSpan> {
        if self.check_keyword(kw) {
            let span = self.current_span();
            self.advance();
            Ok(span)
        } else {
            Err(AlgocError::parser(
                format!("{}, found {}", msg, self.peek().kind),
                self.current_span(),
            ))
        }
    }

    /// Consume token if it matches
    fn match_token(&mut self, kind: &TokenKind) -> bool {
        if self.check(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Consume keyword if it matches
    fn match_keyword(&mut self, kw: Keyword) -> bool {
        if self.check_keyword(kw) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Parse an identifier
    fn parse_ident(&mut self) -> AlgocResult<Ident> {
        match &self.peek().kind {
            TokenKind::Ident(name) => {
                let name = name.clone();
                let span = self.current_span();
                self.advance();
                Ok(Ident::new(name, span))
            }
            _ => Err(AlgocError::parser(
                format!("expected identifier, found {}", self.peek().kind),
                self.current_span(),
            )),
        }
    }

    // ==================== Items ====================

    fn parse_item(&mut self) -> AlgocResult<Item> {
        let start = self.current_span();

        let kind = if self.check_keyword(Keyword::Fn) {
            ItemKind::Function(self.parse_function()?)
        } else if self.check_keyword(Keyword::Struct) {
            ItemKind::Struct(self.parse_struct()?)
        } else if self.check_keyword(Keyword::Layout) {
            ItemKind::Layout(self.parse_layout()?)
        } else if self.check_keyword(Keyword::Const) {
            ItemKind::Const(self.parse_const()?)
        } else if self.check_keyword(Keyword::Test) {
            ItemKind::Test(self.parse_test()?)
        } else {
            return Err(AlgocError::parser(
                format!("expected item (fn, struct, const, test), found {}", self.peek().kind),
                self.current_span(),
            ));
        };

        let span = start.merge(self.previous().span);
        Ok(Item { kind, span })
    }

    fn parse_function(&mut self) -> AlgocResult<Function> {
        self.expect_keyword(Keyword::Fn, "expected 'fn'")?;
        let name = self.parse_ident()?;

        self.expect(&TokenKind::LParen, "expected '(' after function name")?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen, "expected ')' after parameters")?;

        let return_type = if self.match_token(&TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let body = self.parse_block()?;

        Ok(Function {
            name,
            params,
            return_type,
            body,
        })
    }

    fn parse_params(&mut self) -> AlgocResult<Vec<Param>> {
        let mut params = Vec::new();

        if !self.check(&TokenKind::RParen) {
            loop {
                let start = self.current_span();
                let name = self.parse_ident()?;
                self.expect(&TokenKind::Colon, "expected ':' after parameter name")?;
                let ty = self.parse_type()?;
                let span = start.merge(self.previous().span);
                params.push(Param { name, ty, span });

                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
        }

        Ok(params)
    }

    fn parse_struct(&mut self) -> AlgocResult<StructDef> {
        self.expect_keyword(Keyword::Struct, "expected 'struct'")?;
        let name = self.parse_ident()?;

        self.expect(&TokenKind::LBrace, "expected '{' after struct name")?;
        let fields = self.parse_fields()?;
        self.expect(&TokenKind::RBrace, "expected '}' after struct fields")?;

        Ok(StructDef { name, fields })
    }

    fn parse_fields(&mut self) -> AlgocResult<Vec<Field>> {
        let mut fields = Vec::new();

        while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
            let start = self.current_span();
            let name = self.parse_ident()?;
            self.expect(&TokenKind::Colon, "expected ':' after field name")?;
            let ty = self.parse_type()?;

            let mut modifiers = Vec::new();
            while self.match_token(&TokenKind::At) {
                modifiers.push(self.parse_type_modifier()?);
            }

            let span = start.merge(self.previous().span);
            fields.push(Field {
                name,
                ty,
                modifiers,
                span,
            });

            // Comma is optional before closing brace
            if !self.check(&TokenKind::RBrace) {
                self.match_token(&TokenKind::Comma);
            }
        }

        Ok(fields)
    }

    fn parse_type_modifier(&mut self) -> AlgocResult<TypeModifier> {
        let start = self.current_span();

        let kind = if self.match_keyword(Keyword::BigEndian) {
            TypeModifierKind::BigEndian
        } else if self.match_keyword(Keyword::LittleEndian) {
            TypeModifierKind::LittleEndian
        } else if self.match_keyword(Keyword::Packed) {
            TypeModifierKind::Packed
        } else if self.match_keyword(Keyword::Aligned) {
            self.expect(&TokenKind::LParen, "expected '(' after 'aligned'")?;
            let n = self.parse_integer_literal()?;
            self.expect(&TokenKind::RParen, "expected ')' after alignment value")?;
            TypeModifierKind::Aligned(n)
        } else {
            return Err(AlgocError::parser(
                format!("expected type modifier (big_endian, little_endian, aligned, packed), found {}", self.peek().kind),
                self.current_span(),
            ));
        };

        let span = start.merge(self.previous().span);
        Ok(TypeModifier { kind, span })
    }

    fn parse_layout(&mut self) -> AlgocResult<LayoutDef> {
        self.expect_keyword(Keyword::Layout, "expected 'layout'")?;
        let name = self.parse_ident()?;

        self.expect(&TokenKind::LBrace, "expected '{' after layout name")?;

        let mut fields = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
            fields.push(self.parse_layout_field()?);
            self.match_token(&TokenKind::Comma);
        }

        self.expect(&TokenKind::RBrace, "expected '}' after layout fields")?;

        Ok(LayoutDef { name, fields })
    }

    fn parse_layout_field(&mut self) -> AlgocResult<LayoutField> {
        let start = self.current_span();

        self.expect_keyword(Keyword::Bits, "expected 'bits'")?;
        let bits_start = self.parse_integer_literal()?;
        self.expect(&TokenKind::DotDot, "expected '..' in bit range")?;
        let bits_end = self.parse_integer_literal()?;
        self.expect(&TokenKind::Colon, "expected ':' after bit range")?;
        let name = self.parse_ident()?;
        self.expect_keyword(Keyword::As, "expected 'as'")?;
        let ty = self.parse_type()?;

        let span = start.merge(self.previous().span);
        Ok(LayoutField {
            bits_start,
            bits_end,
            name,
            ty,
            span,
        })
    }

    fn parse_const(&mut self) -> AlgocResult<ConstDef> {
        self.expect_keyword(Keyword::Const, "expected 'const'")?;
        let name = self.parse_ident()?;
        self.expect(&TokenKind::Colon, "expected ':' after constant name")?;
        let ty = self.parse_type()?;
        self.expect(&TokenKind::Eq, "expected '=' after constant type")?;
        let value = self.parse_expr()?;
        self.expect(&TokenKind::Semicolon, "expected ';' after constant value")?;

        Ok(ConstDef { name, ty, value })
    }

    fn parse_test(&mut self) -> AlgocResult<TestDef> {
        self.expect_keyword(Keyword::Test, "expected 'test'")?;
        let name = self.parse_ident()?;

        self.expect(&TokenKind::LBrace, "expected '{' after test name")?;

        let mut cases = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
            cases.push(self.parse_test_case()?);
            self.match_token(&TokenKind::Comma);
        }

        self.expect(&TokenKind::RBrace, "expected '}' after test cases")?;

        Ok(TestDef { name, cases })
    }

    fn parse_test_case(&mut self) -> AlgocResult<TestCase> {
        let start = self.current_span();

        let kind = if self.match_keyword(Keyword::Input) {
            self.expect(&TokenKind::Colon, "expected ':' after 'input'")?;
            TestCaseKind::Input(self.parse_expr()?)
        } else if self.match_keyword(Keyword::Expect) {
            self.expect(&TokenKind::Colon, "expected ':' after 'expect'")?;
            TestCaseKind::Expect(self.parse_expr()?)
        } else {
            return Err(AlgocError::parser(
                format!("expected 'input' or 'expect', found {}", self.peek().kind),
                self.current_span(),
            ));
        };

        let span = start.merge(self.previous().span);
        Ok(TestCase { kind, span })
    }

    // ==================== Types ====================

    fn parse_type(&mut self) -> AlgocResult<Type> {
        let start = self.current_span();

        // Reference types: &T, &mut T, &[T], &[T; N]
        if self.match_token(&TokenKind::Amp) {
            if self.match_keyword(Keyword::Mut) {
                let inner = self.parse_type()?;
                let span = start.merge(self.previous().span);
                return Ok(Type {
                    kind: TypeKind::MutRef(Box::new(inner)),
                    span,
                });
            }

            // Could be &T, &[T], or &[T; N]
            if self.match_token(&TokenKind::LBracket) {
                let element = self.parse_type()?;

                if self.match_token(&TokenKind::Semicolon) {
                    // &[T; N]
                    let size = self.parse_integer_literal()?;
                    self.expect(&TokenKind::RBracket, "expected ']' after array size")?;
                    let span = start.merge(self.previous().span);
                    return Ok(Type {
                        kind: TypeKind::ArrayRef {
                            element: Box::new(element),
                            size,
                        },
                        span,
                    });
                } else {
                    // &[T]
                    self.expect(&TokenKind::RBracket, "expected ']' after slice type")?;
                    let span = start.merge(self.previous().span);
                    return Ok(Type {
                        kind: TypeKind::Slice {
                            element: Box::new(element),
                        },
                        span,
                    });
                }
            }

            let inner = self.parse_type()?;
            let span = start.merge(self.previous().span);
            return Ok(Type {
                kind: TypeKind::Ref(Box::new(inner)),
                span,
            });
        }

        // Array type without reference: [T; N]
        if self.match_token(&TokenKind::LBracket) {
            let element = self.parse_type()?;
            self.expect(&TokenKind::Semicolon, "expected ';' in array type [T; N]")?;
            let size = self.parse_integer_literal()?;
            self.expect(&TokenKind::RBracket, "expected ']' after array size")?;
            let span = start.merge(self.previous().span);
            return Ok(Type {
                kind: TypeKind::Array {
                    element: Box::new(element),
                    size,
                },
                span,
            });
        }

        // Primitive types
        if let TokenKind::Keyword(kw) = &self.peek().kind {
            let primitive = match kw {
                Keyword::U8 => Some(PrimitiveType::U8),
                Keyword::U16 => Some(PrimitiveType::U16),
                Keyword::U32 => Some(PrimitiveType::U32),
                Keyword::U64 => Some(PrimitiveType::U64),
                Keyword::U128 => Some(PrimitiveType::U128),
                Keyword::I8 => Some(PrimitiveType::I8),
                Keyword::I16 => Some(PrimitiveType::I16),
                Keyword::I32 => Some(PrimitiveType::I32),
                Keyword::I64 => Some(PrimitiveType::I64),
                Keyword::I128 => Some(PrimitiveType::I128),
                Keyword::Bool => Some(PrimitiveType::Bool),
                _ => None,
            };

            if let Some(p) = primitive {
                self.advance();
                let base_span = self.previous().span;

                // Check for array suffix: T[N]
                if self.match_token(&TokenKind::LBracket) {
                    let size = self.parse_integer_literal()?;
                    self.expect(&TokenKind::RBracket, "expected ']' after array size")?;
                    let span = start.merge(self.previous().span);
                    return Ok(Type {
                        kind: TypeKind::Array {
                            element: Box::new(Type {
                                kind: TypeKind::Primitive(p),
                                span: base_span,
                            }),
                            size,
                        },
                        span,
                    });
                }

                return Ok(Type {
                    kind: TypeKind::Primitive(p),
                    span: base_span,
                });
            }
        }

        // Named type (struct or type alias)
        let name = self.parse_ident()?;
        let span = start.merge(self.previous().span);

        // Check for array suffix
        if self.match_token(&TokenKind::LBracket) {
            let size = self.parse_integer_literal()?;
            self.expect(&TokenKind::RBracket, "expected ']' after array size")?;
            let span = start.merge(self.previous().span);
            return Ok(Type {
                kind: TypeKind::Array {
                    element: Box::new(Type {
                        kind: TypeKind::Named(name),
                        span,
                    }),
                    size,
                },
                span,
            });
        }

        Ok(Type {
            kind: TypeKind::Named(name),
            span,
        })
    }

    fn parse_integer_literal(&mut self) -> AlgocResult<u64> {
        match &self.peek().kind {
            TokenKind::Integer(n) => {
                let n = *n;
                self.advance();
                n.try_into().map_err(|_| {
                    AlgocError::parser("integer literal too large", self.previous().span)
                })
            }
            _ => Err(AlgocError::parser(
                format!("expected integer literal, found {}", self.peek().kind),
                self.current_span(),
            )),
        }
    }

    // ==================== Statements ====================

    fn parse_block(&mut self) -> AlgocResult<Block> {
        let start = self.current_span();
        self.expect(&TokenKind::LBrace, "expected '{'")?;

        let mut stmts = Vec::new();
        while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
            stmts.push(self.parse_stmt()?);
        }

        self.expect(&TokenKind::RBrace, "expected '}'")?;
        let span = start.merge(self.previous().span);

        Ok(Block { stmts, span })
    }

    fn parse_stmt(&mut self) -> AlgocResult<Stmt> {
        let start = self.current_span();

        let kind = if self.check_keyword(Keyword::Let) {
            self.parse_let_stmt()?
        } else if self.check_keyword(Keyword::If) {
            self.parse_if_stmt()?
        } else if self.check_keyword(Keyword::For) {
            self.parse_for_stmt()?
        } else if self.check_keyword(Keyword::While) {
            self.parse_while_stmt()?
        } else if self.check_keyword(Keyword::Loop) {
            self.parse_loop_stmt()?
        } else if self.match_keyword(Keyword::Break) {
            self.expect(&TokenKind::Semicolon, "expected ';' after 'break'")?;
            StmtKind::Break
        } else if self.match_keyword(Keyword::Continue) {
            self.expect(&TokenKind::Semicolon, "expected ';' after 'continue'")?;
            StmtKind::Continue
        } else if self.match_keyword(Keyword::Return) {
            let value = if !self.check(&TokenKind::Semicolon) {
                Some(self.parse_expr()?)
            } else {
                None
            };
            self.expect(&TokenKind::Semicolon, "expected ';' after return")?;
            StmtKind::Return(value)
        } else if self.check(&TokenKind::LBrace) {
            StmtKind::Block(self.parse_block()?)
        } else {
            // Expression or assignment
            self.parse_expr_or_assign_stmt()?
        };

        let span = start.merge(self.previous().span);
        Ok(Stmt { kind, span })
    }

    fn parse_let_stmt(&mut self) -> AlgocResult<StmtKind> {
        self.expect_keyword(Keyword::Let, "expected 'let'")?;

        let mutable = self.match_keyword(Keyword::Mut);
        let name = self.parse_ident()?;

        let ty = if self.match_token(&TokenKind::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let init = if self.match_token(&TokenKind::Eq) {
            Some(self.parse_expr()?)
        } else {
            None
        };

        self.expect(&TokenKind::Semicolon, "expected ';' after let statement")?;

        Ok(StmtKind::Let {
            name,
            ty,
            mutable,
            init,
        })
    }

    fn parse_if_stmt(&mut self) -> AlgocResult<StmtKind> {
        self.expect_keyword(Keyword::If, "expected 'if'")?;
        let condition = self.parse_expr()?;
        let then_block = self.parse_block()?;

        let else_block = if self.match_keyword(Keyword::Else) {
            if self.check_keyword(Keyword::If) {
                // else if - wrap in a block
                let nested_if = self.parse_if_stmt()?;
                let span = self.previous().span;
                Some(Block {
                    stmts: vec![Stmt {
                        kind: nested_if,
                        span,
                    }],
                    span,
                })
            } else {
                Some(self.parse_block()?)
            }
        } else {
            None
        };

        Ok(StmtKind::If {
            condition,
            then_block,
            else_block,
        })
    }

    fn parse_for_stmt(&mut self) -> AlgocResult<StmtKind> {
        self.expect_keyword(Keyword::For, "expected 'for'")?;
        let var = self.parse_ident()?;
        self.expect_keyword(Keyword::In, "expected 'in' after loop variable")?;

        let start = self.parse_expr()?;

        let inclusive = if self.match_token(&TokenKind::DotDotEq) {
            true
        } else if self.match_token(&TokenKind::DotDot) {
            false
        } else {
            return Err(AlgocError::parser(
                "expected '..' or '..=' in for loop range",
                self.current_span(),
            ));
        };

        let end = self.parse_expr()?;
        let body = self.parse_block()?;

        Ok(StmtKind::For {
            var,
            start,
            end,
            inclusive,
            body,
        })
    }

    fn parse_while_stmt(&mut self) -> AlgocResult<StmtKind> {
        self.expect_keyword(Keyword::While, "expected 'while'")?;
        let condition = self.parse_expr()?;
        let body = self.parse_block()?;

        Ok(StmtKind::While { condition, body })
    }

    fn parse_loop_stmt(&mut self) -> AlgocResult<StmtKind> {
        self.expect_keyword(Keyword::Loop, "expected 'loop'")?;
        let body = self.parse_block()?;

        Ok(StmtKind::Loop { body })
    }

    fn parse_expr_or_assign_stmt(&mut self) -> AlgocResult<StmtKind> {
        let expr = self.parse_expr()?;

        // Check for assignment
        if self.match_token(&TokenKind::Eq) {
            let value = self.parse_expr()?;
            self.expect(&TokenKind::Semicolon, "expected ';' after assignment")?;
            return Ok(StmtKind::Assign {
                target: expr,
                value,
            });
        }

        // Check for compound assignment
        let op = match &self.peek().kind {
            TokenKind::PlusEq => Some(BinaryOp::Add),
            TokenKind::MinusEq => Some(BinaryOp::Sub),
            TokenKind::StarEq => Some(BinaryOp::Mul),
            TokenKind::SlashEq => Some(BinaryOp::Div),
            TokenKind::PercentEq => Some(BinaryOp::Rem),
            TokenKind::AmpEq => Some(BinaryOp::BitAnd),
            TokenKind::PipeEq => Some(BinaryOp::BitOr),
            TokenKind::CaretEq => Some(BinaryOp::BitXor),
            TokenKind::LtLtEq => Some(BinaryOp::Shl),
            TokenKind::GtGtEq => Some(BinaryOp::Shr),
            _ => None,
        };

        if let Some(op) = op {
            self.advance();
            let value = self.parse_expr()?;
            self.expect(&TokenKind::Semicolon, "expected ';' after compound assignment")?;
            return Ok(StmtKind::CompoundAssign {
                target: expr,
                op,
                value,
            });
        }

        self.expect(&TokenKind::Semicolon, "expected ';' after expression")?;
        Ok(StmtKind::Expr(expr))
    }

    // ==================== Expressions ====================

    fn parse_expr(&mut self) -> AlgocResult<Expr> {
        self.parse_binary_expr(0)
    }

    fn parse_binary_expr(&mut self, min_prec: u8) -> AlgocResult<Expr> {
        let mut left = self.parse_unary_expr()?;

        loop {
            let op = match &self.peek().kind {
                TokenKind::Plus => BinaryOp::Add,
                TokenKind::Minus => BinaryOp::Sub,
                TokenKind::Star => BinaryOp::Mul,
                TokenKind::Slash => BinaryOp::Div,
                TokenKind::Percent => BinaryOp::Rem,
                TokenKind::Amp => BinaryOp::BitAnd,
                TokenKind::Pipe => BinaryOp::BitOr,
                TokenKind::Caret => BinaryOp::BitXor,
                TokenKind::LtLt => BinaryOp::Shl,
                TokenKind::GtGt => BinaryOp::Shr,
                TokenKind::EqEq => BinaryOp::Eq,
                TokenKind::BangEq => BinaryOp::Ne,
                TokenKind::Lt => BinaryOp::Lt,
                TokenKind::LtEq => BinaryOp::Le,
                TokenKind::Gt => BinaryOp::Gt,
                TokenKind::GtEq => BinaryOp::Ge,
                TokenKind::AmpAmp => BinaryOp::And,
                TokenKind::PipePipe => BinaryOp::Or,
                _ => break,
            };

            let prec = op.precedence();
            if prec < min_prec {
                break;
            }

            self.advance();
            let right = self.parse_binary_expr(prec + 1)?;

            let span = left.span.merge(right.span);
            left = Expr {
                kind: ExprKind::Binary {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                },
                span,
            };
        }

        Ok(left)
    }

    fn parse_unary_expr(&mut self) -> AlgocResult<Expr> {
        let start = self.current_span();

        let op = match &self.peek().kind {
            TokenKind::Minus => Some(UnaryOp::Neg),
            TokenKind::Bang => Some(UnaryOp::Not),
            TokenKind::Tilde => Some(UnaryOp::BitNot),
            TokenKind::Star => {
                self.advance();
                let operand = self.parse_unary_expr()?;
                let span = start.merge(operand.span);
                return Ok(Expr {
                    kind: ExprKind::Deref(Box::new(operand)),
                    span,
                });
            }
            TokenKind::Amp => {
                self.advance();
                if self.match_keyword(Keyword::Mut) {
                    let operand = self.parse_unary_expr()?;
                    let span = start.merge(operand.span);
                    return Ok(Expr {
                        kind: ExprKind::MutRef(Box::new(operand)),
                        span,
                    });
                } else {
                    let operand = self.parse_unary_expr()?;
                    let span = start.merge(operand.span);
                    return Ok(Expr {
                        kind: ExprKind::Ref(Box::new(operand)),
                        span,
                    });
                }
            }
            _ => None,
        };

        if let Some(op) = op {
            self.advance();
            let operand = self.parse_unary_expr()?;
            let span = start.merge(operand.span);
            return Ok(Expr {
                kind: ExprKind::Unary {
                    op,
                    operand: Box::new(operand),
                },
                span,
            });
        }

        self.parse_postfix_expr()
    }

    fn parse_postfix_expr(&mut self) -> AlgocResult<Expr> {
        let mut expr = self.parse_primary_expr()?;

        loop {
            if self.match_token(&TokenKind::LBracket) {
                // Index or Slice: expr[index] or expr[start..end]
                let first = self.parse_expr()?;

                // Check for slice syntax: expr[start..end] or expr[start..=end]
                if self.match_token(&TokenKind::DotDot) {
                    let end = self.parse_expr()?;
                    self.expect(&TokenKind::RBracket, "expected ']' after slice")?;
                    let span = expr.span.merge(self.previous().span);
                    expr = Expr {
                        kind: ExprKind::Slice {
                            array: Box::new(expr),
                            start: Box::new(first),
                            end: Box::new(end),
                            inclusive: false,
                        },
                        span,
                    };
                } else if self.match_token(&TokenKind::DotDotEq) {
                    let end = self.parse_expr()?;
                    self.expect(&TokenKind::RBracket, "expected ']' after slice")?;
                    let span = expr.span.merge(self.previous().span);
                    expr = Expr {
                        kind: ExprKind::Slice {
                            array: Box::new(expr),
                            start: Box::new(first),
                            end: Box::new(end),
                            inclusive: true,
                        },
                        span,
                    };
                } else {
                    // Regular indexing
                    self.expect(&TokenKind::RBracket, "expected ']' after index")?;
                    let span = expr.span.merge(self.previous().span);
                    expr = Expr {
                        kind: ExprKind::Index {
                            array: Box::new(expr),
                            index: Box::new(first),
                        },
                        span,
                    };
                }
            } else if self.match_token(&TokenKind::Dot) {
                // Field access: expr.field
                let field = self.parse_ident()?;
                let span = expr.span.merge(field.span);
                expr = Expr {
                    kind: ExprKind::Field {
                        object: Box::new(expr),
                        field,
                    },
                    span,
                };
            } else if self.match_token(&TokenKind::LParen) {
                // Function call: expr(args)
                let args = self.parse_args()?;
                self.expect(&TokenKind::RParen, "expected ')' after arguments")?;
                let span = expr.span.merge(self.previous().span);
                expr = Expr {
                    kind: ExprKind::Call {
                        func: Box::new(expr),
                        args,
                    },
                    span,
                };
            } else if self.match_keyword(Keyword::As) {
                // Cast: expr as Type
                let ty = self.parse_type()?;
                let span = expr.span.merge(ty.span);
                expr = Expr {
                    kind: ExprKind::Cast {
                        expr: Box::new(expr),
                        ty,
                    },
                    span,
                };
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_args(&mut self) -> AlgocResult<Vec<Expr>> {
        let mut args = Vec::new();

        if !self.check(&TokenKind::RParen) {
            loop {
                args.push(self.parse_expr()?);
                if !self.match_token(&TokenKind::Comma) {
                    break;
                }
            }
        }

        Ok(args)
    }

    fn parse_primary_expr(&mut self) -> AlgocResult<Expr> {
        let start = self.current_span();

        // Integer literal
        if let TokenKind::Integer(n) = &self.peek().kind {
            let n = *n;
            self.advance();
            return Ok(Expr {
                kind: ExprKind::Integer(n),
                span: self.previous().span,
            });
        }

        // String literal
        if let TokenKind::String(s) = &self.peek().kind {
            let s = s.clone();
            self.advance();
            return Ok(Expr {
                kind: ExprKind::String(s),
                span: self.previous().span,
            });
        }

        // Boolean literals
        if self.match_keyword(Keyword::True) {
            return Ok(Expr {
                kind: ExprKind::Bool(true),
                span: self.previous().span,
            });
        }
        if self.match_keyword(Keyword::False) {
            return Ok(Expr {
                kind: ExprKind::Bool(false),
                span: self.previous().span,
            });
        }

        // Built-in functions
        if let Some(builtin) = self.try_parse_builtin() {
            return builtin;
        }

        // bytes() and hex() helpers
        if self.match_keyword(Keyword::Bytes) {
            self.expect(&TokenKind::LParen, "expected '(' after 'bytes'")?;
            let s = match &self.peek().kind {
                TokenKind::String(s) => s.clone(),
                _ => {
                    return Err(AlgocError::parser(
                        "expected string in bytes()",
                        self.current_span(),
                    ))
                }
            };
            self.advance();
            self.expect(&TokenKind::RParen, "expected ')' after bytes argument")?;
            let span = start.merge(self.previous().span);
            return Ok(Expr {
                kind: ExprKind::Bytes(s),
                span,
            });
        }

        if self.match_keyword(Keyword::Hex) {
            self.expect(&TokenKind::LParen, "expected '(' after 'hex'")?;
            let s = match &self.peek().kind {
                TokenKind::String(s) => s.clone(),
                _ => {
                    return Err(AlgocError::parser(
                        "expected string in hex()",
                        self.current_span(),
                    ))
                }
            };
            self.advance();
            self.expect(&TokenKind::RParen, "expected ')' after hex argument")?;
            let span = start.merge(self.previous().span);
            return Ok(Expr {
                kind: ExprKind::Hex(s),
                span,
            });
        }

        // Parenthesized expression or tuple
        if self.match_token(&TokenKind::LParen) {
            let inner = self.parse_expr()?;
            self.expect(&TokenKind::RParen, "expected ')'")?;
            let span = start.merge(self.previous().span);
            return Ok(Expr {
                kind: ExprKind::Paren(Box::new(inner)),
                span,
            });
        }

        // Array literal
        if self.match_token(&TokenKind::LBracket) {
            let mut elements = Vec::new();

            if !self.check(&TokenKind::RBracket) {
                loop {
                    elements.push(self.parse_expr()?);
                    if !self.match_token(&TokenKind::Comma) {
                        break;
                    }
                    // Allow trailing comma
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                }
            }

            self.expect(&TokenKind::RBracket, "expected ']' after array elements")?;
            let span = start.merge(self.previous().span);
            return Ok(Expr {
                kind: ExprKind::Array(elements),
                span,
            });
        }

        // Identifier (possibly struct literal)
        if let TokenKind::Ident(_) = &self.peek().kind {
            let name = self.parse_ident()?;

            // Check for struct literal: Name { field: value, ... }
            // We need to look ahead to distinguish from a block: Name { stmt; }
            // A struct literal has the pattern: Ident { Ident : Expr, ... }
            if self.check(&TokenKind::LBrace) {
                // Look ahead: tokens are { ident : ...
                // pos is at {, pos+1 should be ident, pos+2 should be :
                let is_struct_lit = self.tokens.get(self.pos + 1).is_some_and(|t| {
                    matches!(t.kind, TokenKind::Ident(_))
                }) && self.tokens.get(self.pos + 2).is_some_and(|t| {
                    matches!(t.kind, TokenKind::Colon)
                });

                if is_struct_lit {
                    self.advance(); // consume {
                    let mut fields = Vec::new();

                    while !self.check(&TokenKind::RBrace) && !self.is_at_end() {
                        let field_name = self.parse_ident()?;
                        self.expect(&TokenKind::Colon, "expected ':' after field name")?;
                        let field_value = self.parse_expr()?;
                        fields.push((field_name, field_value));

                        if !self.match_token(&TokenKind::Comma) {
                            break;
                        }
                    }

                    self.expect(&TokenKind::RBrace, "expected '}' after struct fields")?;
                    let span = start.merge(self.previous().span);
                    return Ok(Expr {
                        kind: ExprKind::StructLit { name, fields },
                        span,
                    });
                }
            }

            return Ok(Expr {
                kind: ExprKind::Ident(name.clone()),
                span: name.span,
            });
        }

        Err(AlgocError::parser(
            format!("expected expression, found {}", self.peek().kind),
            self.current_span(),
        ))
    }

    fn try_parse_builtin(&mut self) -> Option<AlgocResult<Expr>> {
        let start = self.current_span();

        let builtin = match &self.peek().kind {
            TokenKind::Keyword(Keyword::Rotr) => Some(BuiltinFunc::Rotr),
            TokenKind::Keyword(Keyword::Rotl) => Some(BuiltinFunc::Rotl),
            TokenKind::Keyword(Keyword::Bswap) => Some(BuiltinFunc::Bswap),
            TokenKind::Keyword(Keyword::ReadU8) => Some(BuiltinFunc::ReadU8),
            TokenKind::Keyword(Keyword::ReadU16Be) => Some(BuiltinFunc::ReadU16Be),
            TokenKind::Keyword(Keyword::ReadU16Le) => Some(BuiltinFunc::ReadU16Le),
            TokenKind::Keyword(Keyword::ReadU32Be) => Some(BuiltinFunc::ReadU32Be),
            TokenKind::Keyword(Keyword::ReadU32Le) => Some(BuiltinFunc::ReadU32Le),
            TokenKind::Keyword(Keyword::ReadU64Be) => Some(BuiltinFunc::ReadU64Be),
            TokenKind::Keyword(Keyword::ReadU64Le) => Some(BuiltinFunc::ReadU64Le),
            TokenKind::Keyword(Keyword::WriteU8) => Some(BuiltinFunc::WriteU8),
            TokenKind::Keyword(Keyword::WriteU16Be) => Some(BuiltinFunc::WriteU16Be),
            TokenKind::Keyword(Keyword::WriteU16Le) => Some(BuiltinFunc::WriteU16Le),
            TokenKind::Keyword(Keyword::WriteU32Be) => Some(BuiltinFunc::WriteU32Be),
            TokenKind::Keyword(Keyword::WriteU32Le) => Some(BuiltinFunc::WriteU32Le),
            TokenKind::Keyword(Keyword::WriteU64Be) => Some(BuiltinFunc::WriteU64Be),
            TokenKind::Keyword(Keyword::WriteU64Le) => Some(BuiltinFunc::WriteU64Le),
            TokenKind::Keyword(Keyword::ConstantTimeEq) => Some(BuiltinFunc::ConstantTimeEq),
            TokenKind::Keyword(Keyword::SecureZero) => Some(BuiltinFunc::SecureZero),
            _ => None,
        };

        let builtin = builtin?;
        self.advance();

        Some((|| {
            self.expect(&TokenKind::LParen, "expected '(' after builtin function")?;
            let args = self.parse_args()?;
            self.expect(&TokenKind::RParen, "expected ')' after arguments")?;

            let span = start.merge(self.previous().span);
            Ok(Expr {
                kind: ExprKind::Builtin { name: builtin, args },
                span,
            })
        })())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(source: &str) -> AlgocResult<Ast> {
        Parser::new(source).parse()
    }

    #[test]
    fn test_parse_const() {
        let ast = parse("const X: u32 = 42;").unwrap();
        assert_eq!(ast.items.len(), 1);
        assert!(matches!(&ast.items[0].kind, ItemKind::Const(_)));
    }

    #[test]
    fn test_parse_struct() {
        let ast = parse(
            r#"
            struct State {
                h: u32[8],
                len: u64
            }
            "#,
        )
        .unwrap();
        assert_eq!(ast.items.len(), 1);
        if let ItemKind::Struct(s) = &ast.items[0].kind {
            assert_eq!(s.name.name, "State");
            assert_eq!(s.fields.len(), 2);
        } else {
            panic!("expected struct");
        }
    }

    #[test]
    fn test_parse_function() {
        let ast = parse(
            r#"
            fn add(a: u32, b: u32) -> u32 {
                return a + b;
            }
            "#,
        )
        .unwrap();
        assert_eq!(ast.items.len(), 1);
        if let ItemKind::Function(f) = &ast.items[0].kind {
            assert_eq!(f.name.name, "add");
            assert_eq!(f.params.len(), 2);
            assert!(f.return_type.is_some());
        } else {
            panic!("expected function");
        }
    }

    #[test]
    fn test_parse_for_loop() {
        let ast = parse(
            r#"
            fn example() {
                for i in 0..16 {
                    x = i;
                }
            }
            "#,
        )
        .unwrap();
        assert_eq!(ast.items.len(), 1);
    }

    #[test]
    fn test_parse_builtin() {
        let ast = parse(
            r#"
            fn example() {
                let x = rotr(val, 7);
            }
            "#,
        )
        .unwrap();
        assert_eq!(ast.items.len(), 1);
    }

    #[test]
    fn test_parse_test() {
        let ast = parse(
            r#"
            test sha256_empty {
                input: bytes(""),
                expect: hex("e3b0c442")
            }
            "#,
        )
        .unwrap();
        assert_eq!(ast.items.len(), 1);
        if let ItemKind::Test(t) = &ast.items[0].kind {
            assert_eq!(t.name.name, "sha256_empty");
            assert_eq!(t.cases.len(), 2);
        } else {
            panic!("expected test");
        }
    }
}
