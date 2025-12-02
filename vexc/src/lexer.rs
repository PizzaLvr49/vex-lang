use std::{iter::Peekable, num::ParseFloatError, str};
use thiserror::Error;

#[derive(Debug)]
pub enum Literal {
    String(String),
    Number(f64),
    Bool(bool),
}

#[derive(Debug)]
pub enum Token {
    Let,
    Equals,
    Identifier(String),
    Literal(Literal),
    Semicolon,
    Eof,
}

#[derive(Debug, Error)]
pub enum LexError {
    #[error("unexpected character: '{0}'")]
    UnexpectedChar(char),

    #[error("unterminated string literal")]
    UnterminatedString,

    #[error("invalid number literal: {0}")]
    InvalidNumber(#[from] ParseFloatError),
}

pub struct Lexer<'a> {
    chars: Peekable<str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
        }
    }

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
