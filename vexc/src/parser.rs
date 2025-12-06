#![expect(missing_docs)]

use crate::lexer::{Literal, Token};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOp {
    Add,
    Sub,
    Div,
    Mul,
    Eq,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Literal(Literal),
    Identifier(String),
    Binary {
        left: Box<Expression>,
        op: BinaryOp,
        right: Box<Expression>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    VarDeclaration { name: String, value: Expression },
    Expression(Expression),
}

/// Errors that can occur during parsing.
#[derive(Debug, Error)]
pub enum ParseError {
    /// An unexpected token was found while parsing.
    ///
    /// This error occurs when a token was encountered that did not match what was expected
    /// at a given point in the grammar.
    ///
    /// # Examples
    ///
    /// Expected token: `=`, found: `+`
    #[error("unexpected token: expected {expected}, found {found:?}")]
    UnexpectedToken {
        /// Description of the expected token.
        expected: String,
        /// The actual token encountered.
        found: Token,
    },

    /// The end of input was reached unexpectedly.
    ///
    /// This error occurs when input ends before parsing is complete, e.g. when an expression is unfinished.
    #[error("unexpected end of file")]
    UnexpectedEOF,

    /// An invalid expression was encountered.
    ///
    /// This error occurs when the parser cannot construct a valid expression from the tokens encountered.
    #[error("invalid expression")]
    InvalidExpression,
}
