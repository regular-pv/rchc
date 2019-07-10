use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;
use std::fmt;
use ta::{
    NoLabel,
    bottom_up::{Automaton}
};
use automatic::Convoluted;
use crate::{
    Clause,
    rich,
    environment::{TypedConstructor, Predicate}
};
use super::{Teacher, Result};

pub enum Error {
    //
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "error")
    }
}

type F = TypedConstructor;
type P = Rc<Predicate>;

/// A simple teacher that explores automata runs to check guesses.
pub struct Explorer {
    // ...
}

impl Explorer {
    pub fn new() -> Explorer {
        Explorer {
            //
        }
    }

    /// For a given pattern p, let's name \omega the ordered list of variables
    /// occuring in the pattern.
    /// This function returns a new predicate P such that for all fresh variable x
    /// and instance \sigma,
    /// if P(x\sigma, \omega\sigma) then x\sigma = p\sigma.
    ///
    /// This function is used to simplify the clauses, so that each predicate application
    /// only contains variables or terms, but no patterns.
    pub fn equality_predicate(pattern: &terms::Pattern<F, usize>) -> P {
        panic!("TODO equality_predicate")
    }
}

pub type Q = usize;

impl<F: Clone, P: Clone + Eq + Hash> Teacher<F, P, Automaton<Convoluted<F>, Q, NoLabel>> for Explorer {
    type Model = HashMap<P, Automaton<Convoluted<F>, Q, NoLabel>>;
    type Error = Error;

    /// Add a new clause to the solver.
    fn assert(&mut self, clause: rich::Clause<F, P>) -> std::result::Result<(), Error> {
        // clause.align(&Explorer::equality_predicate);
        clause.align();
        panic!("TODO assert")
    }

    /// Check a given model.
    /// If it is found to be unsat, gives a non-empty set of learning constraints violated by
    /// the model.
    fn check(&mut self, model: &Self::Model) -> std::result::Result<Result<F, P>, Error> {
        // for clause in self.clauses.iter() {
        //     // ...
        // }

        panic!("TODO check")
    }
}
