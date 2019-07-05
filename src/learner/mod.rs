/// A CHC learner.
///
/// Provides a trait for CHC learners, responsible for guessing new predicates from the learning
/// data provided by a teacher.

use std::collections::HashMap;
use std::hash::Hash;
use std::fmt;
use terms::Term;
use automatic::Convoluted;

pub mod smt;
pub use smt::SMTLearner;

/// Learning sample.
pub struct Sample<P, F>(P, Term<Convoluted<F>>);

/// Learning constraints.
pub enum Constraint<F, P> {
    /// A positive example where the given sample should evaluate to True.
    Positive(Sample<P, F>),

    /// A negative constraint where one of the given samples should evaluate to False.
    Negative(Vec<Sample<P, F>>),

    /// An implication constraint where if all the left hand side samples evaluate to True,
    /// then so should the right hand side sample.
    Implication(Vec<Sample<P, F>>, Sample<P, F>)
}

pub trait Model<P, T> {
    fn get(&self, p: &P) -> &T;
}

impl<P: Eq + Hash, T> Model<P, T> for HashMap<P, T> {
    fn get(&self, p: &P) -> &T {
        HashMap::get(self, p).unwrap()
    }
}

/// Learner trait.
pub trait Learner<F, P, T> {
    type Model: Model<P, T>;
    type Error: fmt::Display;

    /// Declare a new predicate to learn.
    fn declare_predicate(&mut self, p: &P) -> Result<(), Self::Error>;

    /// Add a learning constraint.
    fn add(&mut self, new_constraint: Constraint<F, P>) -> Result<(), Self::Error>;

    /// Produce a model that respects all the constraints given to the learner.
    fn produce_model(&mut self) -> Result<Option<Self::Model>, Self::Error>;
}
