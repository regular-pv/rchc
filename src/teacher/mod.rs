/// A CHC teacher.
///
/// Provides a trait for CHC teachers, responsible for checking learner guesses and finding new
/// learning samples.

use crate::Clause;

pub mod explorer;
pub use explorer::Explorer;

/// Teacher trait.
pub trait Teacher {
    fn assert(&self, clause: Clause);
}
