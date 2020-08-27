//! A CHC teacher.
//!
//! Provides a trait for CHC teachers, responsible for checking learner guesses and finding new
//! learning samples.

use std::fmt;

use crate::clause::Clause;
pub use crate::learner::{Model, Sample, Constraint};

pub mod explorer;
pub use explorer::Explorer;

pub struct Options {
	pub learn_fast: bool,
	pub max_states: usize
}

impl Default for Options {
	fn default() -> Options {
		Options {
			learn_fast: false,
			max_states: std::usize::MAX
		}
	}
}

/// Teacher check results.
pub enum Result<F: fmt::Debug, P: fmt::Debug> {
	Sat,
	Unsat(Vec<Constraint<F, P>>),
	Unknown
}

/// Teacher trait.
pub trait Teacher<S: Clone + PartialEq, F: Clone + fmt::Debug, P: Clone + fmt::Debug, T> {
	type Model: Model<P, T>;
	type Error: fmt::Display;

	/// Add a new clause to the solver.
	fn assert(&mut self, clause: Clause<S, F, P>) -> std::result::Result<(), Self::Error>;

	/// Check a given model.
	/// If it is found to be unsat, gives a non-empty set of learning constraints violated by
	/// the model.
	fn check(&mut self, model: &Self::Model) -> std::result::Result<Result<F, P>, Self::Error>;
}
