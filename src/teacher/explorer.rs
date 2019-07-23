use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;
use std::fmt;
use std::cell::Cell;
use std::marker::PhantomData;
use terms::{
    Pattern,
    Var
};
use ta::{
    Symbol,
    State,
    Rank,
    NoLabel,
    bottom_up::{Automaton},
};
use automatic::{
    Convoluted,
    Convolution,
    MaybeBottom
};
use smt2::GroundSort;
use crate::{
    clause,
    environment::{TypedConstructor, Sort, ConvolutedSort}
};
use super::{Teacher, Constraint, Sample, Result};

pub enum Error {
    //
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "error")
    }
}

type F = TypedConstructor;
type P = Rc<crate::environment::Predicate>;

pub struct Relation<F: Symbol, Q: State, C: Convolution<F>>(pub Automaton<Rank<Convoluted<F>>, Q, NoLabel>, pub PhantomData<C>);

impl<F: Symbol + fmt::Display, Q: State + fmt::Display, C: Convolution<F>> fmt::Display for Relation<F, Q, C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<F: Symbol, Q: State, C: Convolution<F>> crate::engine::ToInstance<F> for Relation<F, Q, C> {
    fn to_instance(&self) -> crate::engine::Instance<F> {
        let alt = C::generic_automaton(&self.0);

        let mut map = HashMap::new();
        for (i, q) in alt.states().enumerate() {
            map.insert(q.clone(), i as u32);
        }

        crate::engine::Instance {
            automaton: alt.map_states(|q| *map.get(q).unwrap()),
            comments: format!("{}", self.0)
        }
    }
}

pub struct PrimitiveData {
    primitive: clause::Primitive<GroundSort<Arc<Sort>>>,
    automaton: Automaton<Rank<Convoluted<F>>, Q, NoLabel>,
    complement: Option<Automaton<Rank<Convoluted<F>>, Q, NoLabel>>
}

/// A simple teacher that explores automata runs to check guesses.
pub struct Explorer<C: Convolution<F>> {
    /// Known predicate, and their assigned index.
    predicates: HashMap<P, usize>,

    /// Known CHC clauses.
    clauses: Vec<Clause>,

    /// Computed primitives.
    primitives: Vec<PrimitiveData>,

    c: PhantomData<C>
}

pub enum Expr {
    True,
    False,
    Apply(Predicate, Convoluted<Pattern<F, usize>>)
}

pub enum Predicate {
    Primitive(usize),
    User(P, usize)
}

pub struct Clause {
    body: Vec<Expr>,
    head: Expr
}

impl<C: Convolution<F>> Explorer<C> {
    pub fn new() -> Explorer<C> {
        Explorer {
            predicates: HashMap::new(),
            clauses: Vec::new(),
            primitives: Vec::new(),
            c: PhantomData
        }
    }

    /// Return the assigned index of a known predicate.
    fn index_of(&self, p: &P) -> Option<usize> {
        if let Some(index) = self.predicates.get(p) {
            Some(*index)
        } else {
            None
        }
    }

    fn compile_clause_expr(&mut self, e: clause::Expr<GroundSort<Arc<Sort>>, F, P>) -> Expr {
        match e {
            clause::Expr::True => Expr::True,
            clause::Expr::False => Expr::False,
            clause::Expr::Var(_) => {
                panic!("TODO variable")
            },
            clause::Expr::Apply(clause::Predicate::User(p), patterns) => {
                let index = if let Some(index) = self.index_of(&p) {
                    index
                } else {
                    let index = self.predicates.len();
                    self.predicates.insert(p.clone(), index);
                    index
                };

                let patterns = patterns.into_iter().map(|p| MaybeBottom::Some(p)).collect();
                let convoluted_pattern = Convoluted(patterns);
                Expr::Apply(Predicate::User(p, index), convoluted_pattern)
            },
            clause::Expr::Apply(clause::Predicate::Primitive(primitive), patterns) => {
                let patterns = patterns.into_iter().map(|p| MaybeBottom::Some(p)).collect();
                let convoluted_pattern = Convoluted(patterns);
                Expr::Apply(Predicate::Primitive(self.get_primitve_index(primitive)), convoluted_pattern)
            }
        }
    }

    pub fn get_primitve_index(&mut self, p: clause::Primitive<GroundSort<Arc<Sort>>>) -> usize {
        for (i, known) in self.primitives.iter().enumerate() {
            if known.primitive == p {
                return i
            }
        }

        let i = self.primitives.len();
        let data = PrimitiveData {
            primitive: p.clone(),
            automaton: match p {
                clause::Primitive::Eq(sort, n) => {
                    let domain = sort.automaton();
                    C::equality(domain, n)
                }
            },
            complement: None
        };

        self.primitives.push(data);
        i
    }

    /// For a given pattern p, let's name \omega the ordered list of variables
    /// occuring in the pattern.
    /// This function returns a new predicate P such that for all fresh variable x
    /// and instance \sigma,
    /// if P(x\sigma, \omega\sigma) then x\sigma = p\sigma.
    ///
    /// This function is used to simplify the clauses, so that each predicate application
    /// only contains variables or terms, but no patterns.
    pub fn equality_predicate(_pattern: &terms::Pattern<F, usize>) -> P {
        panic!("TODO equality_predicate")
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum Q {
    Alive(ConvolutedSort, u32),
    Dead(ConvolutedSort)
}

impl From<ConvolutedSort> for Q {
    fn from(convoluted: ConvolutedSort) -> Q {
        Q::Dead(convoluted)
    }
}

impl From<Q> for ConvolutedSort {
    fn from(q: Q) -> ConvolutedSort {
        match q {
            Q::Alive(convoluted, _) => convoluted,
            Q::Dead(convoluted) => convoluted
        }
    }
}

impl fmt::Display for Q {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Q::Alive(sort, i) => write!(f, "{}:{}", i, sort),
            Q::Dead(sort) => write!(f, "_:{}", sort)
        }
    }
}

impl<C: Convolution<F>> Teacher<GroundSort<Arc<Sort>>, F, P, Relation<F, Q, C>> for Explorer<C> {
    type Model = HashMap<P, Relation<F, Q, C>>;
    type Error = Error;

    /// Add a new clause to the solver.
    fn assert(&mut self, clause: crate::clause::Clause<GroundSort<Arc<Sort>>, F, P>) -> std::result::Result<(), Error> {
        let mut body = Vec::with_capacity(clause.body.len());
        for e in clause.body {
            body.push(self.compile_clause_expr(e));
        }

        let head = self.compile_clause_expr(clause.head);

        self.clauses.push(Clause {
            body: body,
            head: head
        });

        Ok(())
    }

    /// Check a given model.
    /// If it is found to be unsat, gives a non-empty set of learning constraints violated by
    /// the model.
    fn check<'a>(&mut self, model: &'a Self::Model) -> std::result::Result<Result<F, P>, Error> {
        // println!("NEW CHECK");

        let mut automata: Vec<&'a Automaton<Rank<Convoluted<F>>, Q, NoLabel>> = Vec::with_capacity(self.predicates.len());

        for _ in 0..self.predicates.len() {
            unsafe {
                automata.push(std::mem::uninitialized());
            }
        }

        for (p, aut) in model.iter() {
            if let Some(i) = self.index_of(p) {
                automata[i] = &aut.0;
            }
            // non-indexed predicates are not important.
        }

        let mut head_automata = Vec::with_capacity(self.clauses.len());

        let learning_constraints = crossbeam_utils::thread::scope(|scope| {
           let mut threads = Vec::with_capacity(self.clauses.len());

            for clause in &self.clauses {
                let mut head_automaton;

                match &clause.head {
                    Expr::True => panic!("todo Expr::True"),
                    Expr::False => {
                        head_automaton = Automaton::new();
                    },
                    Expr::Apply(Predicate::User(p, p_index), _) => {
                        let domain = p.domain();
                        let alphabet = domain.alphabet();

                        head_automaton = automata[*p_index].clone();

                        // println!("complete automaton\n{} with domain\n{}", head_automaton, domain);

                        head_automaton.complete_with(alphabet.iter(), domain);
                        head_automaton.complement();
                    },
                    Expr::Apply(Predicate::Primitive(p), _) => {
                        panic!("TODO eq automaton")
                    }
                }

                head_automata.push(head_automaton);
            }

            for (k, clause) in self.clauses.iter().enumerate() {
                let mut clause_automata = Vec::with_capacity(clause.body.len()+1);
                let mut patterns = Vec::with_capacity(clause.body.len()+1);

                for e in &clause.body {
                    match e {
                        Expr::True => panic!("todo Expr::True"),
                        Expr::False => panic!("todo Expr::False"),
                        Expr::Apply(Predicate::User(_, p_index), pattern) => {
                            clause_automata.push(automata[*p_index]);
                            patterns.push(pattern.clone());
                        },
                        Expr::Apply(Predicate::Primitive(p), pattern) => {
                            panic!("Eq automaton");
                            patterns.push(pattern.clone());
                        }
                    }
                }

                match &clause.head {
                    Expr::True => panic!("todo Expr::True"),
                    Expr::False => (),
                    Expr::Apply(_, pattern) => {
                        clause_automata.push(&head_automata[k]);
                        patterns.push(pattern.clone());
                    }
                }

                // println!("clause:");
                // for (i, aut) in clause_automata.iter().enumerate() {
                //     println!("aut: {}", aut);
                //     println!("pattern: {}", patterns[i]);
                // }

                let handle = scope.spawn(move |_| {
                    // Make the variable Spawnable.
                    let namespace: Cell<usize> = Cell::new(0);
                    let namespace_ref = &namespace;

                    let searchable_patterns: Vec<Convoluted<Pattern<TypedConstructor, Var<usize>>>> = patterns.into_iter().map(|pattern| {
                        Convoluted(pattern.0.into_iter().map(|conv_pattern| {
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

                    {
                        let terms = C::search(&clause_automata, searchable_patterns).next();
                        // if let Some(terms) = &terms {
                        //     println!("found {}", crate::utils::PList(&terms, ","));
                        // } else {
                        //     println!("empty");
                        // }
                        terms
                    }
                    //None
                });

                threads.push(handle);
            }

            let mut learning_constraints = Vec::new();
            for (i, handle) in threads.into_iter().enumerate() {
                if let Some(mut convoluted_terms) = handle.join().unwrap() {
                    let clause = &self.clauses[i];

                    if clause.body.is_empty() {
                        // positive example.
                        match &clause.head {
                            Expr::Apply(Predicate::User(p, _), _) => {
                                let sample = convoluted_terms.pop().unwrap();
                                let constraint = Constraint::Positive(Sample(p.clone(), sample));
                                learning_constraints.push(constraint);
                            },
                            Expr::Apply(_, _) => {
                                panic!("found a positive example for a primitive!")
                            },
                            _ => unreachable!()
                        }
                    } else {
                        match &clause.head {
                            Expr::Apply(Predicate::User(head_p, _), _) => {
                                // implication constraint.
                                let head_t = convoluted_terms.pop().unwrap();
                                let head_sample = Sample(head_p.clone(), head_t);

                                let mut samples = Vec::new();
                                convoluted_terms.reverse();
                                for e in &clause.body {
                                    match e {
                                        Expr::True => (),
                                        Expr::Apply(Predicate::User(p, _), _) => {
                                            let t = convoluted_terms.pop().unwrap();
                                            samples.push(Sample(p.clone(), t))
                                        },
                                        Expr::Apply(_, _) => {
                                            convoluted_terms.pop().unwrap();
                                            // ignore what we already know.
                                        },
                                        Expr::False => unreachable!()
                                    }
                                }

                                let constraint = Constraint::Implication(samples, head_sample);
                                learning_constraints.push(constraint);
                            },
                            Expr::False | Expr::Apply(_, _) => {
                                let mut samples = Vec::new();
                                convoluted_terms.reverse();
                                for e in &clause.body {
                                    match e {
                                        Expr::True => (),
                                        Expr::Apply(Predicate::User(p, _), _) => {
                                            let t = convoluted_terms.pop().unwrap();
                                            samples.push(Sample(p.clone(), t))
                                        },
                                        Expr::Apply(_, _) => {
                                            convoluted_terms.pop().unwrap();
                                            // ignore what we already know.
                                        },
                                        Expr::False => unreachable!()
                                    }
                                }

                                let constraint = Constraint::Negative(samples);
                                learning_constraints.push(constraint);
                            },
                            Expr::True => unreachable!()
                        }
                    }
                }
            }

            learning_constraints
        }).unwrap();

        if learning_constraints.is_empty() {
            Ok(Result::Sat)
        } else {
            Ok(Result::Unsat(learning_constraints))
        }
    }
}
