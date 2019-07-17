use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::sync::Arc;
use std::marker::PhantomData;
use std::fmt;
use terms::Term;
use ta::{
    NoLabel,
    Symbol,
    Rank,
    bottom_up::{Automaton, Configuration}
};
use automatic::{Convolution, Convoluted, MaybeBottom};
use smt2::{Server, Environment, client::FunctionSignature, GroundSort};
use crate::{Sorted, ConvolutedSort};
use crate::utils::PList;

use super::{Learner, Constraint, Sample};

pub trait Predicate = Clone + Eq + Hash + fmt::Display;

pub type Result<T, K: Clone + PartialEq, P: Predicate> = std::result::Result<T, Error<K, P>>;

pub enum Error<K: Clone + PartialEq, P: Predicate> {
    Solver(SolverError<K, P>),
    // Unsat,
    Unknown
}

impl<K: Clone + PartialEq, P: Predicate> From<SolverError<K, P>> for Error<K, P> {
    fn from(e: SolverError<K, P>) -> Error<K, P> {
        Error::Solver(e)
    }
}

impl<K: Clone + PartialEq, P: Predicate> fmt::Display for Error<K, P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Solver(e) => write!(f, "{}", e),
            // Error::Unsat => write!(f, "SMT-solver response to (check-sat) was `unsat`"),
            Error::Unknown => write!(f, "SMT-solver response to (check-sat) was `unknown`")
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Function<P: Predicate> {
    True,
    False,
    Eq,
    Not,
    Or,
    Q(ConvolutedSort, u32),
    Predicate(P)
}

impl<P: Predicate + fmt::Display> fmt::Display for Function<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Function::True => write!(f, "true"),
            Function::False => write!(f, "false"),
            Function::Eq => write!(f, "="),
            Function::Not => write!(f, "not"),
            Function::Or => write!(f, "or"),
            Function::Q(sort, i) => write!(f, "q{}:{}", i, sort),
            Function::Predicate(p) => write!(f, "p{}", p)
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    Bool,
    Q
}

impl smt2::client::Sort for Sort {
    fn arity(&self) -> usize {
        0
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::Q => write!(f, "Q")
        }
    }
}

pub type Solver<K: Clone + PartialEq, P> = smt2::Client<&'static str, K, Sort, Function<P>>;
pub type SolverError<K: Clone + PartialEq, P> = smt2::client::Error<&'static str, K, Sort, Function<P>>;

pub struct SMTLearner<K: Clone + PartialEq, F: Symbol, P: Predicate, C: Convolution<F>> {
    automaton: Vec<Automaton<Rank<Convoluted<F>>, AbsQ, NoLabel>>,
    solver: Solver<K, P>,
    namespace: Namespace,
    const_sort: smt2::GroundSort<Sort>,
    predicate_ids: HashMap<P, u32>,
    c: PhantomData<C>
}

pub trait Constructor = Symbol + Eq + Hash + Sorted<GroundSort<Arc<crate::Sort>>>;

/// States of the abstract automaton.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsQ(ConvolutedSort, u32);

impl fmt::Display for AbsQ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub type Q = crate::teacher::explorer::Q;

impl AbsQ {
    pub fn as_fun<P: Predicate>(&self) -> Function<P> {
        Function::Q(self.0.clone(), self.1)
    }
}

pub struct Namespace {
    count: u32
}

impl Namespace {
    pub fn new() -> Namespace {
        Namespace {
            count: 0
        }
    }

    pub fn spawn(&mut self, sort: ConvolutedSort) -> AbsQ {
        let id = self.count;
        self.count += 1;
        AbsQ(sort, id)
    }
}

impl<K: Clone + PartialEq + fmt::Display, F: Constructor, P: Predicate, C: Convolution<F>> SMTLearner<K, F, P, C> {
    pub fn new(mut solver: Solver<K, P>) -> SMTLearner<K, F, P, C> {
        let const_sort = smt2::GroundSort::new(Sort::Q);
        solver.declare_sort(Sort::Q);
        solver.predefined_fun("=", Function::Eq, FunctionSignature::LogicBinary);
        solver.predefined_fun("not", Function::Not, FunctionSignature::LogicUnary);
        solver.predefined_fun("or", Function::Or, FunctionSignature::LogicNary);
        SMTLearner {
            automaton: Vec::new(),
            namespace: Namespace::new(),
            solver: solver,
            const_sort: const_sort,
            predicate_ids: HashMap::new(),
            c: PhantomData
        }
    }

    fn predicate_id(&self, predicate: &P) -> u32 {
        *self.predicate_ids.get(predicate).unwrap()
    }

    fn op(&self, op: Function<P>, args: Vec<smt2::Term<Solver<K, P>>>) -> smt2::Term<Solver<K, P>> {
        smt2::Term::apply(op, args, self.solver.sort_bool())
    }

    fn as_term(&self, q: &AbsQ) -> smt2::Term<Solver<K, P>> {
        smt2::Term::apply(q.as_fun(), Vec::new(), self.const_sort.clone())
    }

    fn declare_transition(&mut self, predicate: u32, Configuration(f, states): &Configuration<Rank<Convoluted<F>>, AbsQ>, q: AbsQ) -> Result<(), K, P> {
        self.solver.declare_const(q.as_fun(), &self.const_sort)?;
        for (Configuration(other_f, other_states), _, other_q) in self.automaton[predicate as usize].transitions() {
            if f == other_f {
                let mut clause = vec![self.op(Function::Eq, vec![self.as_term(&q), self.as_term(other_q)])];
                for (i, sub_state) in states.iter().enumerate() {
                    let other_sub_state = other_states[i].clone();
                    clause.push(self.op(Function::Not, vec![self.op(Function::Eq, vec![self.as_term(sub_state), self.as_term(&other_sub_state)])]));
                }

                self.solver.assert(&self.op(Function::Or, clause))?
            }
        }

        Ok(())
    }

    fn add_term(&mut self, predicate: u32, term: Term<Rank<Convoluted<F>>>) -> Result<AbsQ, K, P> {
        let namespace = &mut self.namespace;
        let mut new_transitons = Vec::new();
        let term_q = self.automaton[predicate as usize].add_normalized(&term, &mut |configuration| {
            let convoluted_f = configuration.symbol();
            let mut conv_sort = Vec::with_capacity(convoluted_f.0.len());
            for f in convoluted_f.0.iter() {
                let sort = match f {
                    MaybeBottom::Bottom => MaybeBottom::Bottom,
                    MaybeBottom::Some(f) => MaybeBottom::Some(f.sort().clone())
                };
                conv_sort.push(sort);
            }

            let q = namespace.spawn(Convoluted(conv_sort));
            new_transitons.push((configuration.clone(), q.clone()));
            (q, NoLabel)
        });

        for (configuration, q) in new_transitons.drain(..) {
            self.declare_transition(predicate, &configuration, q)?
        }

        Ok(term_q)
    }

    fn add_sample(&mut self, Sample(predicate, term): Sample<P, F>) -> Result<AbsQ, K, P> {
        self.add_term(self.predicate_id(&predicate), term)
    }

    fn assert_positive(&mut self, p: P, q: AbsQ) -> Result<(), K, P> {
        self.solver.assert(&self.op(Function::Predicate(p.clone()), vec![self.as_term(&q)]))?;
        Ok(())
    }

    fn assert_negative(&mut self, states: &[AbsQ]) -> Result<(), K, P> {
        panic!("TODO assert_negative")
    }

    fn assert_implication(&mut self, lhs: &[AbsQ], rhs: AbsQ) -> Result<(), K, P> {
        panic!("TODO assert_implication")
    }

    fn decode_predicate_definition(final_states: &mut HashSet<u32>, term: &smt2::Term<Solver<K, P>>) {
        match term {
            smt2::Term::Apply { fun, .. } => {
                match fun {
                    Function::False => (),
                    _ => panic!("TODO decode predicate definition")
                }
            },
            _ => panic!("TODO decode predicate definition")
        }
    }
}

/// Learner trait.
impl<K: Clone + PartialEq + fmt::Display, F: Constructor, P: Predicate, C: Convolution<F>> Learner<F, P, Automaton<Rank<Convoluted<F>>, Q, NoLabel>> for SMTLearner<K, F, P, C> {
    type Model = HashMap<P, Automaton<Rank<Convoluted<F>>, Q, NoLabel>>;
    type Error = Error<K, P>;

    /// Declare a new predicate to learn.
    fn declare_predicate(&mut self, p: P) -> Result<(), K, P> {
        let index = self.automaton.len() as u32;
        self.predicate_ids.insert(p.clone(), index);
        self.automaton.push(Automaton::new());

        Ok(self.solver.declare_fun(Function::Predicate(p), &vec![self.const_sort.clone()], &self.solver.sort_bool())?)
    }

    /// Add a learning constraint.
    fn add(&mut self, new_constraint: Constraint<F, P>) -> Result<(), K, P> {
        match new_constraint {
            Constraint::Positive(sample) => {
                let p = sample.0.clone();
                let q = self.add_sample(sample)?;
                self.assert_positive(p, q)
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
    fn produce_model(&mut self) -> Result<Option<Self::Model>, K, P> {
        match self.solver.check_sat()? {
            smt2::response::CheckSat::Sat => {
                let smt_model = self.solver.get_model()?;
                let mut model = HashMap::new();

                for def in smt_model.definitions.iter() {
                    for (i, decl) in def.declarations.iter().enumerate() {
                        let body = &def.bodies[i];
                        match &decl.f {
                            Function::Q(sort, i) => {
                                panic!("TODO abs-q defintion")
                            },
                            Function::Predicate(p) => {
                                let mut final_states = HashSet::new();
                                Self::decode_predicate_definition(&mut final_states, body);

                                let mut aut = Automaton::new();
                                for final_q in &final_states {
                                    panic!("TODO add final state");
                                }

                                model.insert(p.clone(), aut);
                            },
                            _ => ()
                        }
                    }
                }

                Ok(Some(model))
            },
            smt2::response::CheckSat::Unsat => Ok(None),
            smt2::response::CheckSat::Unknown => Err(Error::Unknown)
        }
    }
}
