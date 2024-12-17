// Copyright (c) Facebook, Inc. and its affiliates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! This crate provides a generic parser for SMT2 commands, as specified by the
//! [SMT-LIB-2 standard](http://smtlib.cs.uiowa.edu/language.shtml).
//!
//! Commands are parsed and immediately visited by a user-provided
//! implementation of the trait [`visitors::Smt2Visitor`].
//!
//! To obtain concrete syntax values, use [`concrete::SyntaxBuilder`] as a
//! visitor:
//! ```
//! # use smt2parser::{CommandStream, concrete};
//! let input = b"(echo \"Hello world!\")(exit)";
//! let stream = CommandStream::new(
//!     &input[..],
//!     concrete::SyntaxBuilder,
//!     Some("optional/path/to/file".to_string()),
//! );
//! let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
//! assert!(matches!(commands[..], [
//!     concrete::Command::Echo {..},
//!     concrete::Command::Exit,
//! ]));
//! assert_eq!(commands[0].to_string(), "(echo \"Hello world!\")");
//! ```

#![forbid(unsafe_code)]

#[macro_use]
extern crate pomelo;

pub mod concrete;
pub mod let_extract;
mod lexer;
mod parser;
pub mod renaming;
pub mod rewriter;
pub mod stats;
pub mod visitors;
pub mod vmt;

/// SMT2 numeral values.
pub type Numeral = num::bigint::BigUint;
/// SMT2 decimal values.
pub type Decimal = num::rational::BigRational;
/// A base-16 digit.
pub type Nibble = u8;
/// SMT2 hexadecimal values.
pub type Hexadecimal = Vec<Nibble>;
/// SMT2 binary values.
pub type Binary = Vec<bool>;

use std::{fs::File, io::BufReader, path::PathBuf};

/// A minimal error type.
pub use concrete::Error;
use concrete::{Command, SyntaxBuilder, Term};
/// A position in the input.
pub use lexer::Position;
use vmt::{VMTError, VMTModel};

pub fn get_vmt_from_path(input: &PathBuf) -> Result<VMTModel, VMTError> {
    let filename = String::from(input.to_str().unwrap());
    let content = std::io::BufReader::new(std::fs::File::open(input).unwrap());
    let commands = get_commands(content, filename);
    VMTModel::checked_from(commands)
}

pub fn get_commands(content: BufReader<File>, filename: String) -> Vec<Command> {
    let command_stream = CommandStream::new(content, SyntaxBuilder, Some(filename));
    let mut commands = vec![];
    for result in command_stream {
        match result {
            Ok(command) => commands.push(command),
            Err(err) => todo!("Command Error: {}", err),
        }
    }
    commands
}

pub fn get_term_from_term_string(term: &str) -> Term {
    // Adding the `assert` here doesn't do anything, it just allows us to
    // call CommandStream to build a term easily.
    let command_string = format!("(assert {})", term);
    get_term_from_assert_command_string(command_string.as_bytes())
}

pub fn get_term_from_assert_command_string(assert_command: &[u8]) -> Term {
    let stream = CommandStream::new(assert_command, SyntaxBuilder, None);
    let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
    match &commands[0] {
            Command::Assert { term } => term.clone(),
            _ => panic!("Didn't give `get_term_from_assert_command_string` a string beginning with a command: {:?}", commands),
        }
}

/// Parses the given &[u8] as a Command. Panics if more than one Command
/// was parsed from the input string.
pub fn get_command_from_command_string(command: &[u8]) -> Command {
    let stream = CommandStream::new(command, SyntaxBuilder, None);
    let commands = stream.collect::<Result<Vec<_>, _>>().unwrap();
    assert!(
        commands.len() == 1,
        "Gave `get_command_from_command_string()` more than one Command!"
    );
    commands[0].clone()
}

/// Parse the input data and return a stream of interpreted SMT2 commands
pub struct CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    lexer: lexer::Lexer<R>,
    visitor: T,
    position: Position,
}

impl<R, T> CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    pub fn new(reader: R, visitor: T, path: Option<String>) -> Self {
        Self {
            lexer: lexer::Lexer::new(reader),
            visitor,
            position: Position {
                path,
                ..Position::default()
            },
        }
    }

    pub fn visitor(&self) -> &T {
        &self.visitor
    }

    pub fn visitor_mut(&mut self) -> &mut T {
        &mut self.visitor
    }

    pub fn into_visitor(self) -> T {
        self.visitor
    }
}

impl<R, T> Iterator for CommandStream<R, T>
where
    R: std::io::BufRead,
    T: visitors::Smt2Visitor,
{
    type Item = Result<T::Command, T::Error>;

    #[allow(clippy::while_let_on_iterator)]
    fn next(&mut self) -> Option<Result<T::Command, T::Error>> {
        let mut parser = parser::Parser::new((&mut self.visitor, &mut self.position));
        let mut unmatched_paren = 0;
        while let Some(token) = self.lexer.next() {
            match &token {
                parser::Token::LeftParen => unmatched_paren += 1,
                parser::Token::RightParen => {
                    if unmatched_paren > 0 {
                        unmatched_paren -= 1;
                    }
                }
                _ => (),
            }
            self.lexer.update_position(parser.extra_mut().1);
            if let Err(err) = parser.parse(token) {
                return Some(Err(err));
            }
            if unmatched_paren == 0 {
                return match parser.end_of_input() {
                    Ok((command, _)) => Some(Ok(command)),
                    Err(err) => Some(Err(err)),
                };
            }
        }
        if unmatched_paren > 0 {
            // We ran out of valid tokens in the middle of a command.
            let extra = parser.into_extra();
            Some(Err(extra.0.parsing_error(
                extra.1.clone(),
                "unexpected end of input".into(),
            )))
        } else {
            // There are no more valid tokens to parse.
            // TODO: report invalid tokens as an error.
            None
        }
    }
}

#[test]
fn test_command_stream_error() {
    let input = b"(echo \"Hello world!\")(exit f)";
    let builder = concrete::SyntaxBuilder;
    let stream = CommandStream::new(&input[..], builder, None);
    let commands = stream.collect::<Vec<_>>();
    assert!(matches!(
        commands[..],
        [
            Ok(concrete::Command::Echo { .. }),
            Err(concrete::Error::SyntaxError(..)),
            Err(concrete::Error::SyntaxError(..)),
        ]
    ));
    assert_eq!(
        commands[0].as_ref().unwrap().to_string(),
        "(echo \"Hello world!\")"
    );
}

#[test]
fn test_command_stream_invalid_token() {
    let input = b"(echo \"Hello world!\")(exit \x0000)";
    let builder = concrete::SyntaxBuilder;
    let stream = CommandStream::new(&input[..], builder, None);
    let commands = stream.collect::<Vec<_>>();
    assert!(matches!(
        commands[..],
        [
            Ok(concrete::Command::Echo { .. }),
            Err(concrete::Error::ParsingError(..)),
        ]
    ));
    assert_eq!(
        commands[0].as_ref().unwrap().to_string(),
        "(echo \"Hello world!\")"
    );
}
