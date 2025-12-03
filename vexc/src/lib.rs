//! # Vex Compiler
//!
//! A compiler for the Vex programming language.
//!
//! ## Overview
//!
//! The Vex compiler (`vexc`) transforms Vex source code into executable programs
//! through a series of compilation phases.
//!
//! ## Modules
//!
//! - [`lexer`] - Tokenizes source code into lexical tokens
//! - (Future: `parser` - Builds abstract syntax trees)
//! - (Future: `codegen` - Generates target code)
//!
//! ## Quick Start
//!
//! ```
//! use vexc::lexer::{Lexer, Token};
//!
//! let mut lexer = Lexer::new("let x = 42;");
//! loop {
//!     match lexer.next_token() {
//!         Ok(Token::Eof) => break,
//!         Ok(token) => println!("{:?}", token),
//!         Err(e) => {
//!             eprintln!("Error: {}", e);
//!             break;
//!         }
//!     }
//! }
//! ```
//!
//! ## Compilation Pipeline
//!
//! 1. **Lexical Analysis** - Source text → Tokens
//! 2. **Parsing** - Tokens → AST (coming soon)
//! 3. **Semantic Analysis** - Type checking (coming soon)
//! 4. **Code Generation** - AST → Target code (coming soon)

#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]

//! # Additional Module Information
//!
//! This crate is organized into several key modules:
//!
//! ## Core Compiler Modules
//!
//! - [`lexer`] - Lexical analysis and tokenization

/// Lexical analyzer for tokenizing Vex source code.
///
/// See the [module documentation](lexer) for detailed usage.
pub mod lexer;
/// yap
pub mod parser;
