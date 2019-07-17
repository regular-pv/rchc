use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;
use std::sync::Arc;
use std::fmt;
use std::cell::Cell;
use terms::{
    Pattern,
    Var
};
use ta::{
    Rank,
    NoLabel,
    bottom_up::{Automaton},
};
use automatic::{
    Convoluted,
    Convolution,
    MaybeBottom,
    convolution::aligned::{
        self,
        AlignedConvolutedPattern,
        multi_search
    }
};
use crate::{
    rich,
    environment::{TypedConstructor, Predicate, Sort, ConvolutedSort}
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
type P = Rc<Predicate>;

/// A simple teacher that explores automata runs to check guesses.
pub struct Explorer {
    /// Known predicate, and their assigned index.
    predicates: HashMap<P, usize>,

    /// Known CHC clauses.
    clauses: Vec<Clause>,
}

pub enum Expr {
    True,
    False,
    Apply(P, usize, AlignedConvolutedPattern<F, usize>)
}

pub struct Clause {
    body: Vec<Expr>,
    head: Expr
}

impl Explorer {
    pub fn new() -> Explorer {
        Explorer {
            predicates: HashMap::new(),
            clauses: Vec::new()
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

    fn compile_clause_expr(&mut self, e: rich::Expr<F, P>) -> Expr {
        match e {
            rich::Expr::True => Expr::True,
            rich::Expr::False => Expr::False,
            rich::Expr::Var(_) => {
                panic!("TODO variable")
            },
            rich::Expr::Apply(p, patterns) => {
                let index = if let Some(index) = self.index_of(&p) {
                    index
                } else {
                    let index = self.predicates.len();
                    self.predicates.insert(p.clone(), index);
                    index
                };

                let patterns = patterns.into_iter().map(|p| MaybeBottom::Some(p)).collect();
                let convoluted_pattern = AlignedConvolutedPattern(patterns);
                Expr::Apply(p.clone(), index, convoluted_pattern)
            }
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

impl Teacher<F, P, Automaton<Rank<Convoluted<F>>, Q, NoLabel>> for Explorer {
    type Model = HashMap<P, Automaton<Rank<Convoluted<F>>, Q, NoLabel>>;
    type Error = Error;

    /// Add a new clause to the solver.
    fn assert(&mut self, mut clause: rich::Clause<F, P>) -> std::result::Result<(), Error> {
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
        let mut automata: Vec<&'a Automaton<Rank<Convoluted<F>>, Q, NoLabel>> = Vec::with_capacity(self.predicates.len());

        for _ in 0..self.predicates.len() {
            unsafe {
                automata.push(std::mem::uninitialized());
            }
        }

        for (p, aut) in model.iter() {
            if let Some(i) = self.index_of(p) {
                automata[i] = aut;
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
                    Expr::False => panic!("todo Expr::False"),
                    Expr::Apply(p, p_index, pattern) => {
                        let domain = p.domain();
                        let alphabet = domain.alphabet();

                        head_automaton = automata[*p_index].clone();
                        head_automaton.complete_with(alphabet.iter(), domain);
                        head_automaton.complement();
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
                        Expr::Apply(_, p_index, pattern) => {
                            clause_automata.push(automata[*p_index]);
                            patterns.push(pattern.clone());
                        }
                    }
                }

                match &clause.head {
                    Expr::True => panic!("todo Expr::True"),
                    Expr::False => panic!("todo Expr::False"),
                    Expr::Apply(p, p_index, pattern) => {
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

                    let searchable_patterns: Vec<AlignedConvolutedPattern<TypedConstructor, Var<usize>>> = patterns.into_iter().map(|pattern| {
                        AlignedConvolutedPattern(pattern.0.into_iter().map(|conv_pattern| {
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
                        let terms = multi_search(&clause_automata, searchable_patterns).next();
                        // if let Some(terms) = terms {
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
                        // positive example
                        if let Expr::Apply(p, _, _) = &clause.head {
                            let sample = convoluted_terms.pop().unwrap();
                            let constraint = Constraint::Positive(Sample(p.clone(), sample));
                            learning_constraints.push(constraint);
                        } else {
                            unreachable!()
                        }
                    } else {
                        panic!("TODO other constraints")
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
