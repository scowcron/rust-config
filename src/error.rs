//! Errors that can occur while parsing a configuration

use std::error::Error;
use std::fmt;
use std::io::Error as IoError;
use parser::ParseError;

/// A generic configuration error type
#[derive(Debug)]
pub struct ConfigError {
    /// Indicates what kind of error this is
    pub kind: ErrorKind,
    /// A descriptive message about the error
    pub desc: &'static str,
    /// Error details, if available
    pub detail: Option<String>,

    err_desc: String
}

/// Possible error kinds
#[derive(Debug)]
#[derive(PartialEq)]
pub enum ErrorKind {
    /// An I/O error. Can only occur if reading from a stream (file, socket, etc.)
    IoError,
    /// A syntax error
    ParseError
}

impl ConfigError {
    fn new<E: fmt::Display>(kind: ErrorKind, desc: &'static str, err: E) -> ConfigError {
        let err_desc = format!("{:?} {}: {}", kind, desc, err);
        ConfigError {
            kind: kind,
            desc: desc,
            detail: Some(format!("{}", err)),

            err_desc: err_desc
        }
    }
}

impl From<IoError> for ConfigError {
    fn from(err: IoError) -> ConfigError {
        ConfigError::new(ErrorKind::IoError, "An I/O error has occurred", err)
    }
}

impl From<ParseError> for ConfigError {
    fn from(err: ParseError) -> ConfigError {
        ConfigError::new(ErrorKind::ParseError, "Syntax error", err)
    }
}

impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{}", self.description()));
        Ok(())
    }
}

impl Error for ConfigError {
    fn description(&self) -> &str {
        &self.err_desc[..]
    }
}
