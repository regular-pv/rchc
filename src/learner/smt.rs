use std::collections::HashMap;
use std::hash::Hash;
use std::marker::PhantomData;
use std::fmt;
use terms::Term;
use ta::{
    NoLabel,
    Symbol,
    bottom_up::{Automaton, Configuration}
};
use automatic::{Convolution, Convoluted};
use smt2::{Server, Environment};

use super::{Learner, Constraint, Sample};

pub type Result<T> = std::result::Result<T, Error>;

pub enum Error {
    Solver(SolverError),
    Unsat,
    Unknown
}

impl From<SolverError> for Error {
    fn from(e: SolverError) -> Error {
        Error::Solver(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Solver(e) => write!(f, "{}", e),
            Error::Unsat => write!(f, "SMT-solver response to (check-sat) was `unsat`"),
            Error::Unknown => write!(f, "SMT-solver response to (check-sat) was `unknown`")
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum Ident {
    Raw(&'static str),
    Fresh(&'static str, usize)
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ident::Raw(name) => write!(f, "{}", name),
            Ident::Fresh(prefix, id) => write!(f, "{}{}", prefix, id)
        }
    }
}

impl From<&'static str> for Ident {
    fn from(name: &'static str) -> Ident {
        Ident::Raw(name)
    }
}

pub type Function = Ident;

pub type Solver = smt2::Client<&'static str, Ident, &'static str, Function>;
pub type SolverError = smt2::client::Error<&'static str, Ident, &'static str, Function>;

pub struct SMTLearner<F: Symbol, P, C: Convolution<F>> {
    automaton: Vec<Automaton<Convoluted<F>, AbsQ, NoLabel>>,
    solver: Solver,
    namespace: Namespace,
    const_sort: smt2::GroundSort<&'static str>,
    predicate_ids: HashMap<P, usize>,
    c: PhantomData<C>
}

/// States of the abstract automaton.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbsQ(usize);

pub type Q = usize;

impl AbsQ {
    pub fn id(&self) -> Ident {
        Ident::Fresh("q", self.0)
    }

    pub fn as_fun(&self) -> Function {
        self.id() as Function
    }
}

pub struct Namespace {
    count: usize
}

impl Namespace {
    pub fn new() -> Namespace {
        Namespace {
            count: 0
        }
    }

    pub fn spawn(&mut self) -> AbsQ {
        let id = self.count;
        self.count += 1;
        AbsQ(id)
    }
}

impl<F: Symbol + Eq + Hash, P: Clone + Eq + Hash, C: Convolution<F>> SMTLearner<F, P, C> {
    pub fn new(solver: Solver) -> SMTLearner<F, P, C> {
        SMTLearner {
            automaton: Vec::new(),
            namespace: Namespace::new(),
            solver: solver,
            const_sort: smt2::GroundSort::new("Q"),
            predicate_ids: HashMap::new(),
            c: PhantomData
        }
    }

    fn predicate_id(&self, predicate: &P) -> usize {
        *self.predicate_ids.get(predicate).unwrap()
    }

    fn op(&self, op: &'static str, args: Vec<smt2::Term<Solver>>) -> smt2::Term<Solver> {
        smt2::Term::apply(Ident::Raw(op), args, self.solver.sort_bool())
    }

    fn as_term(&self, q: &AbsQ) -> smt2::Term<Solver> {
        smt2::Term::apply(q.as_fun(), Vec::new(), self.const_sort.clone())
    }

    fn declare_transition(&mut self, predicate: usize, Configuration(f, states): &Configuration<Convoluted<F>, AbsQ>, q: AbsQ) -> Result<()> {
        self.solver.declare_const(&q.id(), &self.const_sort)?;
        for (Configuration(other_f, other_states), _, other_q) in self.automaton[predicate].transitions() {
            if f == other_f {
                let mut clause = vec![self.op("=", vec![self.as_term(&q), self.as_term(other_q)])];
                for (i, sub_state) in states.iter().enumerate() {
                    let other_sub_state = other_states[i];
                    clause.push(self.op("not", vec![self.op("=", vec![self.as_term(sub_state), self.as_term(&other_sub_state)])]));
                }

                self.solver.assert(&self.op("or", clause))?
            }
        }

        Ok(())
    }

    fn add_term(&mut self, predicate: usize, term: Term<Convoluted<F>>) -> Result<AbsQ> {
        let namespace = &mut self.namespace;
        let mut new_transitons = Vec::new();
        let term_q = self.automaton[predicate].add_normalized(&term, &mut |configuration| {
            let q = namespace.spawn();
            new_transitons.push((configuration.clone(), q.clone()));
            (q, NoLabel)
        });

        for (configuration, q) in new_transitons.drain(..) {
            self.declare_transition(predicate, &configuration, q)?
        }

        Ok(term_q)
    }

    fn add_sample(&mut self, Sample(predicate, term): Sample<P, F>) -> Result<AbsQ> {
        self.add_term(self.predicate_id(&predicate), term)
    }

    fn assert_positive(&mut self, q: AbsQ) -> Result<()> {
        panic!("TODO assert_positive")
    }

    fn assert_negative(&mut self, states: &[AbsQ]) -> Result<()> {
        panic!("TODO assert_negative")
    }

    fn assert_implication(&mut self, lhs: &[AbsQ], rhs: AbsQ) -> Result<()> {
        panic!("TODO assert_implication")
    }
}

/// Learner trait.
impl<F: Symbol + Eq + Hash, P: Clone + Eq + Hash, C: Convolution<F>> Learner<F, P, Automaton<Convoluted<F>, Q, NoLabel>> for SMTLearner<F, P, C> {
    type Model = HashMap<P, Automaton<Convoluted<F>, Q, NoLabel>>;
    type Error = Error;

    /// Declare a new predicate to learn.
    fn declare_predicate(&mut self, p: &P) -> Result<()> {
        let index = self.automaton.len();
        self.predicate_ids.insert(p.clone(), index);
        self.automaton.push(Automaton::new());
        Ok(self.solver.declare_fun(&Ident::Fresh("p", index), &vec![self.const_sort.clone()], &self.solver.sort_bool())?)
    }

    /// Add a learning constraint.
    fn add(&mut self, new_constraint: Constraint<F, P>) -> Result<()> {
        match new_constraint {
            Constraint::Positive(sample) => {
                let q = self.add_sample(sample)?;
                self.assert_positive(q)
            },
            Constraint::Negative(mut samples) => {
                let mut states = Vec::with_capacity(samples.len());
                for s in samples.drain(..) {
                    states.push(self.add_sample(s)?)
                }
                self.assert_negative(&states)
            },
            Constraint::Implication(mut lhs, rhs) => {
                let mut lhs_states = Vec::with_capacity(lhs.len());
                for s in lhs.drain(..) {
                    lhs_states.push(self.add_sample(s)?)
                }
                let rhs_state = self.add_sample(rhs)?;
                self.assert_implication(&lhs_states, rhs_state)
            }
        }
    }

    /// Produce a model that respects all the constraints given to the learner.
    fn produce_model(&mut self) -> Result<Option<Self::Model>> {
        match self.solver.check_sat()? {
            smt2::response::CheckSat::Sat => {
                panic!("TODO produce model")
            },
            smt2::response::CheckSat::Unsat => Err(Error::Unsat),
            smt2::response::CheckSat::Unknown => Err(Error::Unknown)
        }
    }
}
