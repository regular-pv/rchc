use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;
use std::fmt;
use std::cell::Cell;
use terms::{
    Pattern,
    Var
};
use ta::{
    NoLabel,
    bottom_up::{Automaton},
};
use automatic::{
    Convoluted,
    MaybeBottom,
    convolution::aligned::{
        AlignedConvolutedPattern,
        multi_search
    }
};
use crate::{
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
    /// Known predicate, and their assigned index.
    predicates: HashMap<P, usize>,

    /// Known CHC clauses.
    clauses: Vec<Clause>
}

pub struct Clause {
    patterns: Vec<AlignedConvolutedPattern<F, usize>>
}

impl Explorer {
    pub fn new() -> Explorer {
        Explorer {
            predicates: HashMap::new(),
            clauses: Vec::new()
        }
    }

    /// Return the assigned index of a known predicate.
    /// Panics if the predicate is unknown.
    fn index_of(&self, p: &P) -> usize {
        panic!("TODO index")
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

impl Teacher<F, P, Automaton<Convoluted<F>, Q, NoLabel>> for Explorer {
    type Model = HashMap<P, Automaton<Convoluted<F>, Q, NoLabel>>;
    type Error = Error;

    /// Add a new clause to the solver.
    fn assert(&mut self, clause: rich::Clause<F, P>) -> std::result::Result<(), Error> {
        // clause.align(&Explorer::equality_predicate);
        // clause.align();
        panic!("TODO assert")
    }

    /// Check a given model.
    /// If it is found to be unsat, gives a non-empty set of learning constraints violated by
    /// the model.
    fn check<'a>(&mut self, model: &'a Self::Model) -> std::result::Result<Result<F, P>, Error> {
        // for clause in self.clauses.iter() {
        //     // ...
        // }

        let mut automata: Vec<&'a Automaton<Convoluted<F>, Q, NoLabel>> = Vec::with_capacity(self.predicates.len());
        for _ in 0..self.predicates.len() {
            unsafe {
                automata.push(std::mem::uninitialized());
            }
        }

        for (p, aut) in model.iter() {
            let i = self.index_of(p);
            automata[i] = aut;
        }

        for clause in &self.clauses {
            // Make the variable Spawnable.
            let namespace: Cell<usize> = Cell::new(0);
            let namespace_ref = &namespace;
            let patterns = clause.patterns.iter().map(|pattern| {
                AlignedConvolutedPattern(pattern.0.iter().map(|conv_pattern| {
                    if let MaybeBottom::Some(conv_pattern) = conv_pattern {
                        MaybeBottom::Some(conv_pattern.map_variables(&mut |x| {
                            let max_id = namespace_ref.get();
                            if *x > max_id {
                                namespace_ref.set(*x)
                            }

                            Pattern::var(Var::from(*x, &namespace_ref))
                        }))
                    } else {
                        MaybeBottom::Bottom
                    }
                }).collect())
            }).collect();

            multi_search(&automata, patterns);
        }

        panic!("TODO after check")
    }
}
