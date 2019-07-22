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
    SortedWith,
    bottom_up::{Automaton, Configuration}
};
use automatic::{Convolution, Convoluted, MaybeBottom};
use smt2::{Server, Environment, client::{FunctionSignature, Constant, Sorted}, GroundSort};
use crate::{ConvolutedSort};
use crate::utils::PList;
use crate::teacher::explorer::Relation;

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
            Error::Solver(e) => write!(f, "SMT-solver: {}", e),
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
    And,
    Or,
    Implies,
    Ite,
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
            Function::And => write!(f, "and"),
            Function::Or => write!(f, "or"),
            Function::Implies => write!(f, "=>"),
            Function::Ite => write!(f, "ite"),
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

pub trait Constructor = Symbol + Eq + Hash + SortedWith<GroundSort<Arc<crate::Sort>>>;

/// States of the abstract automaton.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsQ(ConvolutedSort, u32);

impl fmt::Display for AbsQ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "q{}:{}", self.1, self.0)
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

impl<K: Constant + fmt::Display, F: Constructor, P: Predicate, C: Convolution<F>> SMTLearner<K, F, P, C> {
    pub fn new(mut solver: Solver<K, P>) -> SMTLearner<K, F, P, C> {
        let const_sort = smt2::GroundSort::new(Sort::Q);
        solver.declare_sort(Sort::Q);
        solver.predefined_fun("=", Function::Eq, FunctionSignature::Equality);
        solver.predefined_fun("not", Function::Not, FunctionSignature::LogicUnary);
        solver.predefined_fun("and", Function::And, FunctionSignature::LogicNary);
        solver.predefined_fun("or", Function::Or, FunctionSignature::LogicNary);
        solver.predefined_fun("=>", Function::Implies, FunctionSignature::LogicBinary);
        solver.predefined_fun("ite", Function::Ite, FunctionSignature::Ite);
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
        for (Configuration(other_f, other_states), _, other_q) in self.automaton[predicate as usize].transitions() {
            if f == other_f {
                let mut clause = vec![self.op(Function::Eq, vec![self.as_term(&q), self.as_term(other_q)])];
                for (i, sub_state) in states.iter().enumerate() {
                    let other_sub_state = other_states[i].clone();
                    clause.push(self.op(Function::Not, vec![self.op(Function::Eq, vec![self.as_term(sub_state), self.as_term(&other_sub_state)])]));
                }

                let term = self.op(Function::Or, clause);
                self.solver.assert(&term)?
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

        for (configuration, q) in &new_transitons {
            self.solver.declare_const(q.as_fun(), &self.const_sort)?;
        }

        for (configuration, q) in new_transitons.into_iter() {
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

    fn assert_negative(&mut self, states: &[(P, AbsQ)]) -> Result<(), K, P> {
        self.solver.assert(&self.op(Function::Not, vec![
            self.op(Function::And, states.iter().map(|(p, q)| {
                self.op(Function::Predicate(p.clone()), vec![self.as_term(&q)])
            }).collect())
        ]))?;
        Ok(())
    }

    fn assert_implication(&mut self, lhs: &[(P, AbsQ)], rhs: (P, AbsQ)) -> Result<(), K, P> {
        self.solver.assert(&self.op(Function::Implies, vec![
            self.op(Function::And, lhs.iter().map(|(p, q)| {
                self.op(Function::Predicate(p.clone()), vec![self.as_term(&q)])
            }).collect()),
            self.op(Function::Predicate(rhs.0.clone()), vec![self.as_term(&rhs.1)])
        ]))?;
        Ok(())
    }

    fn is_final_state(state: u32, term: &smt2::Term<Solver<K, P>>) -> bool {
        #[derive(PartialEq)]
        enum Value {
            Q(u32),
            Bool(bool)
        }

        fn eval<K: Constant, P: Predicate>(state: u32, term: &smt2::Term<Solver<K, P>>) -> Value {
            match term {
                smt2::Term::Var { .. } => Value::Q(state),
                smt2::Term::Const(Sorted(cst, _)) => {
                    Value::Q(cst.index())
                },
                smt2::Term::Apply { fun: Function::True, .. } => {
                    Value::Bool(true)
                },
                smt2::Term::Apply { fun: Function::False, .. } => {
                    Value::Bool(false)
                },
                smt2::Term::Apply { fun: Function::Eq, args, .. } => {
                    Value::Bool(eval(state, &args[0]) == eval(state, &args[1]))
                },
                smt2::Term::Apply { fun: Function::Ite, args, .. } => {
                    if eval(state, &args[0]) == Value::Bool(true) {
                        eval(state, &args[1])
                    } else {
                        eval(state, &args[2])
                    }
                },
                _ => panic!("invalid state definition term! It may also be unsupported.")
            }
        }

        eval(state, term) == Value::Bool(true)
    }
}

/// Learner trait.
impl<K: Constant + fmt::Display, F: Constructor, P: Predicate, C: Convolution<F>> Learner<F, P, Relation<F, Q, C>> for SMTLearner<K, F, P, C> {
    type Model = HashMap<P, Relation<F, Q, C>>;
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
                    let p = s.0.clone();
                    states.push((p, self.add_sample(s)?))
                }
                self.assert_negative(&states)
            },
            Constraint::Implication(mut lhs, rhs) => {
                let mut lhs_states = Vec::with_capacity(lhs.len());
                for s in lhs.into_iter() {
                    let p = s.0.clone();
                    lhs_states.push((p, self.add_sample(s)?))
                }
                let rhs_p = rhs.0.clone();
                let rhs_state = self.add_sample(rhs)?;
                self.assert_implication(&lhs_states, (rhs_p, rhs_state))
            }
        }
    }

    /// Produce a model that respects all the constraints given to the learner.
    fn produce_model(&mut self) -> Result<Option<Self::Model>, K, P> {
        match self.solver.check_sat()? {
            smt2::response::CheckSat::Sat => {
                let smt_model = self.solver.get_model()?;
                let mut model = HashMap::new();

                let mut table = HashMap::new();
                let mut predicates_defs: Vec<(P, smt2::Term<Solver<K, P>>)> = Vec::new();

                for mut def in smt_model.definitions.into_iter() {
                    def.bodies.reverse();
                    for decl in def.declarations.into_iter() {
                        let body = def.bodies.pop().unwrap();
                        match decl.f {
                            Function::Q(sort, i) => {
                                match body {
                                    smt2::Term::Const(Sorted(c, _)) => {
                                        table.insert(i, c.index());
                                    },
                                    _ => panic!("unexpected state definition!")
                                }
                            },
                            Function::Predicate(p) => {
                                predicates_defs.push((p.clone(), body));
                            },
                            _ => ()
                        }
                    }
                }

                for (p, body) in &predicates_defs {
                    let i = self.predicate_id(p) as usize;
                    let abs_aut = &self.automaton[i];
                    // println!("-----------");
                    // println!("abs_aut: {}", abs_aut);
                    //let mut final_states = HashSet::new();
                    let mut aut = abs_aut.map_states(|AbsQ(sort, k)| {
                        Q::Alive(sort.clone(), *table.get(k).unwrap())
                    });

                    let mut final_states = HashSet::new();
                    for q in aut.states() {
                        if let Q::Alive(sort, k) = q {
                            if Self::is_final_state(*k, body) {
                                final_states.insert(q.clone());
                            }
                        }
                    }

                    for q in final_states.into_iter() {
                        aut.set_final(q);
                    }

                    // println!("aut: {}", aut);
                    // println!("-----------");

                    model.insert(p.clone(), Relation(aut, PhantomData));
                }

                Ok(Some(model))
            },
            smt2::response::CheckSat::Unsat => Ok(None),
            smt2::response::CheckSat::Unknown => Err(Error::Unknown)
        }
    }
}
