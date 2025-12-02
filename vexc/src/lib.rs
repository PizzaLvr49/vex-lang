#![doc = include_str!("../../docs/vexc/index.md")]
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
