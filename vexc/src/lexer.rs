//! Lexical analysis for the Vex language.
//!
//! This module provides the [`Lexer`] type which tokenizes Vex source code into
//! a stream of [`Token`]s that can be consumed by a parser.

use std::{iter::Peekable, num::ParseFloatError, str};
use thiserror::Error;

/// A literal value in Vex source code.
///
/// Literals are constant values that appear directly in the source code,
/// such as numbers, strings, and boolean values.
#[derive(Debug)]
pub enum Literal {
    /// A string literal enclosed in double quotes.
    ///
    /// # Examples
    ///
    /// - `"hello world"`
    /// - `""`
    /// - `"The quick brown fox"`
    String(String),

    /// A numeric literal represented as a 64-bit floating point number.
    ///
    /// Supports both integers and decimal numbers, positive and negative.
    ///
    /// # Examples
    ///
    /// - `42`
    /// - `-3.14159`
    /// - `0.5`
    Number(f64),

    /// A boolean literal, either `true` or `false`.
    Bool(bool),
}

/// A token produced by the lexer.
///
/// Tokens represent the smallest meaningful units of Vex source code after
/// lexical analysis. Each token corresponds to a keyword, operator, literal,
/// identifier, or structural element.
#[derive(Debug)]
pub enum Token {
    /// The `let` keyword used for variable declarations.
    Let,

    /// The equals sign `=` used for assignment.
    Equals,

    /// An identifier such as a variable name.
    ///
    /// Identifiers must start with a letter or underscore, and can contain
    /// letters, digits, and underscores.
    ///
    /// # Examples
    ///
    /// - `myVar`
    /// - `_private`
    /// - `count_123`
    Identifier(String),

    /// A literal value (string, number, or boolean).
    Literal(Literal),

    /// The semicolon `;` used to terminate statements.
    Semicolon,

    /// End of file/input marker.
    ///
    /// This token is returned when there is no more input to process.
    Eof,
}

/// Errors that can occur during lexical analysis.
#[derive(Debug, Error)]
pub enum LexError {
    /// An unexpected character was encountered in the input.
    ///
    /// This error occurs when the lexer encounters a character that doesn't
    /// match any valid token pattern and isn't whitespace.
    ///
    /// # Examples
    ///
    /// Characters like `@`, `#`, `$` will produce this error in most contexts.
    #[error("unexpected character: '{0}'")]
    UnexpectedChar(char),

    /// A string literal was not properly terminated with a closing quote.
    ///
    /// This error occurs when a string starts with `"` but the input ends
    /// before a matching closing `"` is found.
    #[error("unterminated string literal")]
    UnterminatedString,

    /// A numeric literal could not be parsed as a valid number.
    ///
    /// This error is automatically converted from [`ParseFloatError`] and occurs
    /// when the numeric literal has invalid syntax (e.g., multiple decimal points).
    #[error("invalid number literal: {0}")]
    InvalidNumber(#[from] ParseFloatError),
}

/// A lexical analyzer that converts Vex source text into tokens.
///
/// The lexer operates on a borrowed string slice and produces tokens one at a time
/// through the [`next_token`](Lexer::next_token) method. It handles whitespace
/// automatically and recognizes keywords, identifiers, literals, and punctuation.
///
/// # Examples
///
/// ```
/// use vexc::lexer::{Lexer, Token, Literal};
///
/// let mut lexer = Lexer::new("let x = 42;");
///
/// // Tokenize the entire input
/// let token = lexer.next_token().unwrap();
/// assert!(matches!(token, Token::Let));
///
/// let token = lexer.next_token().unwrap();
/// assert!(matches!(token, Token::Identifier(_)));
///
/// let token = lexer.next_token().unwrap();
/// assert!(matches!(token, Token::Equals));
/// ```
///
/// # Supported Syntax
///
/// - **Keywords**: `let`, `true`, `false`
/// - **Operators**: `=`
/// - **Delimiters**: `;`
/// - **Literals**: strings (`"..."`), numbers (`42`, `-3.14`), booleans
/// - **Identifiers**: alphanumeric sequences starting with letter or underscore
pub struct Lexer<'a> {
    /// Peekable iterator over the input characters.
    chars: Peekable<str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    /// Creates a new lexer for the given input string.
    ///
    /// The lexer borrows the input string for its lifetime and does not
    /// allocate unless necessary (e.g., for identifier/string storage).
    ///
    /// # Examples
    ///
    /// ```
    /// use vexc::lexer::Lexer;
    ///
    /// let lexer = Lexer::new("let x = 5;");
    /// ```
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
        }
    }

    /// Consumes and returns the next token from the input.
    ///
    /// This method advances the lexer's position in the input and returns
    /// the next meaningful token, skipping any whitespace. When the end of
    /// input is reached, it returns [`Token::Eof`].
    ///
    /// # Errors
    ///
    /// Returns a [`LexError`] if:
    /// - An unexpected character is encountered ([`LexError::UnexpectedChar`])
    /// - A string literal is not terminated ([`LexError::UnterminatedString`])
    /// - A number literal is malformed ([`LexError::InvalidNumber`])
    ///
    /// # Examples
    ///
    /// ```
    /// use vexc::lexer::{Lexer, Token, Literal};
    ///
    /// let mut lexer = Lexer::new("42");
    /// let token = lexer.next_token().unwrap();
    ///
    /// match token {
    ///     Token::Literal(Literal::Number(n)) => assert_eq!(n, 42.0),
    ///     _ => panic!("Expected number"),
    /// }
    /// ```
    ///
    /// Handling errors:
    ///
    /// ```
    /// use vexc::lexer::{Lexer, LexError};
    ///
    /// let mut lexer = Lexer::new("@");
    /// match lexer.next_token() {
    ///     Err(LexError::UnexpectedChar('@')) => { /* handle error */ }
    ///     _ => panic!("Expected error"),
    /// }
    /// ```
    pub fn next_token(&mut self) -> Result<Token, LexError> {
        self.skip_whitespace();

        let ch = match self.chars.peek() {
            None => return Ok(Token::Eof),
            Some(&c) => c,
        };

        match ch {
            '=' => {
                self.chars.next();
                Ok(Token::Equals)
            }

            ';' => {
                self.chars.next();
                Ok(Token::Semicolon)
            }

            '"' => {
                let s = self.read_string()?;
                Ok(Token::Literal(Literal::String(s)))
            }

            '-' => {
                let mut iter = self.chars.clone();
                iter.next();
                match iter.peek() {
                    Some(c) if c.is_ascii_digit() => {
                        let n = self.read_number()?;
                        Ok(Token::Literal(Literal::Number(n)))
                    }
                    _ => {
                        self.chars.next();
                        Err(LexError::UnexpectedChar('-'))
                    }
                }
            }

            '0'..='9' => {
                let n = self.read_number()?;
                Ok(Token::Literal(Literal::Number(n)))
            }

            c if c.is_alphabetic() || c == '_' => {
                let ident = self.read_identifier();

                match ident.as_str() {
                    "let" => Ok(Token::Let),
                    "true" => Ok(Token::Literal(Literal::Bool(true))),
                    "false" => Ok(Token::Literal(Literal::Bool(false))),
                    _ => Ok(Token::Identifier(ident)),
                }
            }

            other => {
                self.chars.next();
                Err(LexError::UnexpectedChar(other))
            }
        }
    }

    /// Reads an identifier from the current position.
    ///
    /// An identifier starts with a letter or underscore and can contain
    /// letters, digits, and underscores. This method consumes characters
    /// until a non-identifier character is encountered.
    fn read_identifier(&mut self) -> String {
        let mut identifier = String::new();

        while let Some(&ch) = self.chars.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                identifier.push(ch);
                self.chars.next();
            } else {
                break;
            }
        }

        identifier
    }

    /// Reads a string literal from the current position.
    ///
    /// Expects the current character to be a double quote `"`. Consumes
    /// characters until the closing double quote is found.
    ///
    /// # Errors
    ///
    /// Returns [`LexError::UnterminatedString`] if the input ends before
    /// a closing quote is found.
    fn read_string(&mut self) -> Result<String, LexError> {
        let mut output = String::new();

        if self.chars.peek() != Some(&'"') {
            return Err(LexError::UnterminatedString);
        }
        self.chars.next();

        for ch in &mut self.chars {
            if ch == '"' {
                return Ok(output);
            } else {
                output.push(ch);
            }
        }

        Err(LexError::UnterminatedString)
    }

    /// Reads a numeric literal from the current position.
    ///
    /// Consumes digits, decimal points, and minus signs to form a number.
    /// The resulting string is parsed as an f64.
    ///
    /// # Errors
    ///
    /// Returns [`LexError::InvalidNumber`] if the collected characters
    /// cannot be parsed as a valid f64.
    fn read_number(&mut self) -> Result<f64, LexError> {
        let mut buf = String::new();

        while let Some(&ch) = self.chars.peek() {
            if ch.is_ascii_digit() || ch == '.' || ch == '-' {
                buf.push(ch);
                self.chars.next();
            } else {
                break;
            }
        }

        let parsed = buf.parse::<f64>()?;
        Ok(parsed)
    }

    /// Skips whitespace characters from the current position.
    ///
    /// Advances the character iterator past any whitespace (spaces, tabs,
    /// newlines, etc.) until a non-whitespace character is encountered or
    /// the end of input is reached.
    fn skip_whitespace(&mut self) {
        while let Some(&ch) = self.chars.peek() {
            if ch.is_whitespace() {
                self.chars.next();
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
mod test {

    use super::*;

    #[test]
    fn test_empty_input() {
        let mut lexer = Lexer::new("");
        let token = lexer.next_token().unwrap();
        assert!(matches!(token, Token::Eof));
    }

    #[test]
    fn test_whitespace_only() {
        let mut lexer = Lexer::new("   \t\n  ");
        let token = lexer.next_token().unwrap();
        assert!(matches!(token, Token::Eof));
    }

    #[test]
    fn test_let_keyword() {
        let mut lexer = Lexer::new("let");
        let token = lexer.next_token().unwrap();
        assert!(matches!(token, Token::Let));
    }

    #[test]
    fn test_equals() {
        let mut lexer = Lexer::new("=");
        let token = lexer.next_token().unwrap();
        assert!(matches!(token, Token::Equals));
    }

    #[test]
    fn test_semicolon() {
        let mut lexer = Lexer::new(";");
        let token = lexer.next_token().unwrap();
        assert!(matches!(token, Token::Semicolon));
    }

    #[test]
    fn test_identifier() {
        let mut lexer = Lexer::new("myVar");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Identifier(s) => assert_eq!(s, "myVar"),
            _ => panic!("Expected identifier"),
        }
    }

    #[test]
    fn test_identifier_with_underscore() {
        let mut lexer = Lexer::new("_my_var_123");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Identifier(s) => assert_eq!(s, "_my_var_123"),
            _ => panic!("Expected identifier"),
        }
    }

    #[test]
    fn test_string_literal() {
        let mut lexer = Lexer::new(r#""hello world""#);
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::String(s)) => assert_eq!(s, "hello world"),
            _ => panic!("Expected string literal"),
        }
    }

    #[test]
    fn test_empty_string() {
        let mut lexer = Lexer::new(r#""""#);
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::String(s)) => assert_eq!(s, ""),
            _ => panic!("Expected empty string literal"),
        }
    }

    #[test]
    fn test_unterminated_string() {
        let mut lexer = Lexer::new(r#""hello"#);
        let result = lexer.next_token();
        assert!(matches!(result, Err(LexError::UnterminatedString)));
    }

    #[test]
    fn test_positive_integer() {
        let mut lexer = Lexer::new("42");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::Number(n)) => assert_eq!(n, 42.0),
            _ => panic!("Expected number literal"),
        }
    }

    #[test]
    fn test_negative_integer() {
        let mut lexer = Lexer::new("-42");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::Number(n)) => assert_eq!(n, -42.0),
            _ => panic!("Expected number literal"),
        }
    }

    #[test]
    fn test_float() {
        let mut lexer = Lexer::new("2.14159");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::Number(n)) => assert_eq!(n, 2.14159),
            _ => panic!("Expected number literal"),
        }
    }

    #[test]
    fn test_negative_float() {
        let mut lexer = Lexer::new("-2.5");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::Number(n)) => assert_eq!(n, -2.5),
            _ => panic!("Expected number literal"),
        }
    }

    #[test]
    fn test_bool_true() {
        let mut lexer = Lexer::new("true");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::Bool(b)) => assert!(b),
            _ => panic!("Expected bool literal"),
        }
    }

    #[test]
    fn test_bool_false() {
        let mut lexer = Lexer::new("false");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::Bool(b)) => assert!(!b),
            _ => panic!("Expected bool literal"),
        }
    }

    #[test]
    fn test_unexpected_character() {
        let mut lexer = Lexer::new("@");
        let result = lexer.next_token();
        assert!(matches!(result, Err(LexError::UnexpectedChar('@'))));
    }

    #[test]
    fn test_standalone_minus() {
        let mut lexer = Lexer::new("-");
        let result = lexer.next_token();
        assert!(matches!(result, Err(LexError::UnexpectedChar('-'))));
    }

    #[test]
    fn test_simple_statement() {
        let mut lexer = Lexer::new("let x = 42;");

        let token1 = lexer.next_token().unwrap();
        assert!(matches!(token1, Token::Let));

        let token2 = lexer.next_token().unwrap();
        match token2 {
            Token::Identifier(s) => assert_eq!(s, "x"),
            _ => panic!("Expected identifier"),
        }

        let token3 = lexer.next_token().unwrap();
        assert!(matches!(token3, Token::Equals));

        let token4 = lexer.next_token().unwrap();
        match token4 {
            Token::Literal(Literal::Number(n)) => assert_eq!(n, 42.0),
            _ => panic!("Expected number"),
        }

        let token5 = lexer.next_token().unwrap();
        assert!(matches!(token5, Token::Semicolon));

        let token6 = lexer.next_token().unwrap();
        assert!(matches!(token6, Token::Eof));
    }

    #[test]
    fn test_string_statement() {
        let mut lexer = Lexer::new(r#"let name = "Alice";"#);

        assert!(matches!(lexer.next_token().unwrap(), Token::Let));

        match lexer.next_token().unwrap() {
            Token::Identifier(s) => assert_eq!(s, "name"),
            _ => panic!("Expected identifier"),
        }

        assert!(matches!(lexer.next_token().unwrap(), Token::Equals));

        match lexer.next_token().unwrap() {
            Token::Literal(Literal::String(s)) => assert_eq!(s, "Alice"),
            _ => panic!("Expected string"),
        }

        assert!(matches!(lexer.next_token().unwrap(), Token::Semicolon));
    }

    #[test]
    fn test_multiple_statements() {
        let mut lexer = Lexer::new("let x = 10; let y = 20;");

        assert!(matches!(lexer.next_token().unwrap(), Token::Let));
        assert!(matches!(lexer.next_token().unwrap(), Token::Identifier(_)));
        assert!(matches!(lexer.next_token().unwrap(), Token::Equals));
        assert!(matches!(
            lexer.next_token().unwrap(),
            Token::Literal(Literal::Number(_))
        ));
        assert!(matches!(lexer.next_token().unwrap(), Token::Semicolon));

        assert!(matches!(lexer.next_token().unwrap(), Token::Let));
        assert!(matches!(lexer.next_token().unwrap(), Token::Identifier(_)));
        assert!(matches!(lexer.next_token().unwrap(), Token::Equals));
        assert!(matches!(
            lexer.next_token().unwrap(),
            Token::Literal(Literal::Number(_))
        ));
        assert!(matches!(lexer.next_token().unwrap(), Token::Semicolon));

        assert!(matches!(lexer.next_token().unwrap(), Token::Eof));
    }

    #[test]
    fn test_zero() {
        let mut lexer = Lexer::new("0");
        let token = lexer.next_token().unwrap();
        match token {
            Token::Literal(Literal::Number(n)) => assert_eq!(n, 0.0),
            _ => panic!("Expected zero"),
        }
    }

    #[test]
    fn test_whitespace_variations() {
        let mut lexer = Lexer::new("let\tx\n=\r\n42;");

        assert!(matches!(lexer.next_token().unwrap(), Token::Let));
        assert!(matches!(lexer.next_token().unwrap(), Token::Identifier(_)));
        assert!(matches!(lexer.next_token().unwrap(), Token::Equals));
        assert!(matches!(
            lexer.next_token().unwrap(),
            Token::Literal(Literal::Number(_))
        ));
        assert!(matches!(lexer.next_token().unwrap(), Token::Semicolon));
    }
}
