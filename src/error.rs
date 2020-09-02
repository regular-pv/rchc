use std::fmt;
use source_span::Span;

/// Runtime errors.
pub enum Error {
	/// For non-HORN assertions.
	InvalidAssertion(Span, InvalidAssertionReason),

	/// For non-Bool predicates.
	InvalidPredicateReturnType,

	/// Model is not ready
	NoModel,

	Engine(crate::engine::Error)
}

pub enum InvalidAssertionReason {
	AssertForallBody,
	Expr,
	ExprNot,
	Pattern,
	InvalidEquiv(Span, Span)
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
			InvalidAssertion(_, _) => write!(f, "invalid assertion"),
			InvalidPredicateReturnType => write!(f, "invalid predicate return type"),
			NoModel => write!(f, "model is not ready"),
			Engine(e) => write!(f, "engine: {}", e)
		}
	}
}

impl smt2::error::Informative for Error {
	fn informations(&self, i: &mut smt2::error::Infos) {
		use Error::*;
		use InvalidAssertionReason::*;
		match self {
			InvalidAssertion(span, reason) => {
				match reason {
					AssertForallBody => {
						i.add(*span, Some("the `forall` construct can only contain an implication, a negation or a conjunction of predicate application".to_string()))
					},
					Expr => {
						i.add(*span, Some("this must be a predicate or primitive application".to_string()))
					},
					ExprNot => {
						i.add(*span, Some("only predicate applications are allowed under `not`".to_string()))
					},
					Pattern => {
						i.add(*span, Some("this must be a pattern".to_string()))
					},
					InvalidEquiv(span_a, span_b) => {
						i.add(*span_a, Some("either this should be a predicate application...".to_string()));
						i.add(*span_b, Some("...or this".to_string()));
						i.add_note("\x1b[1mnote:\x1b[m the equivalence operator `<=>` expects a simple predicate application on one side".to_string())
					}
				}
			},
			InvalidPredicateReturnType => {
				i.add_note("\x1b[1mhelp:\x1b[m predicates must return a `Bool`".to_string())
			},
			NoModel => {
				i.add_note("\x1b[1mhelp:\x1b[m use the `(check-sat)` command to generate a model".to_string())
			},
			_ => ()
		}
	}
}
