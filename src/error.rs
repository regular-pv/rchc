use std::fmt;

/// Runtime errors.
pub enum Error {
    /// For non-HORN assertions.
    InvalidAssertion,

    /// For non-Bool predicates.
    InvalidPredicateReturnType,

    Engine(crate::engine::Error)
}

impl From<crate::engine::Error> for Error {
    fn from(e: crate::engine::Error) -> Error {
        Error::Engine(e)
    }
}

pub type Result<T> = smt2::ExecResult<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            InvalidAssertion => write!(f, "invalid assertion"),
            InvalidPredicateReturnType => write!(f, "invalid predicate return type"),
            Engine(e) => write!(f, "engine: {}", e)
        }
    }
}
