use std::rc::Rc;
use smt2::Function as SMT2Function;
use smt2::Environment as SMT2Environment;
use automatic::MaybeBottom;
use super::{Environment, Predicate, Function, Ident, Convoluted};

enum Node<F: Clone + PartialEq, T> {
    Leaf(T),
    Node {
        f: F,
        next: Box<Vec<Node<F, T>>>
    }
}

impl<F: Clone + PartialEq, T> Node<F, T> {
    pub fn add(&mut self, list: &[F], value: T) {
        match self {
            Node::Node { ref mut next, .. } => {
                match list.split_first() {
                    Some((head, tail)) => {
                        for n in next.iter_mut() {
                            if let Node::Node { f, .. } = n {
                                if f == head {
                                    return n.add(tail, value)
                                }
                            }
                        }

                        let n = Node::Node {
                            f: head.clone(),
                            next: Box::new(Vec::new())
                        };

                        next.push(n);
                        next.last_mut().unwrap().add(tail, value)
                    },
                    None => {
                        next.push(Node::Leaf(value))
                    }
                }
            },
            Node::Leaf(_) => unreachable!()
        }
    }
}

pub struct MatchGraph<F: Clone + PartialEq, T> {
    roots: Vec<Node<F, T>>,
    len: usize
}

impl<F: Clone + PartialEq, T> MatchGraph<F, T> {
    pub fn new() -> MatchGraph<F, T> {
        MatchGraph {
            roots: Vec::new(),
            len: 0
        }
    }

    pub fn add(&mut self, list: &[F], value: T) {
        if self.len == 0 {
            self.len = list.len();
        } else {
            if list.len() != self.len {
                panic!("all inputs must have the same length!")
            }
        }
        match list.split_first() {
            Some((head, tail)) => {
                for n in self.roots.iter_mut() {
                    if let Node::Node { f, .. } = n {
                        if f == head {
                            return n.add(tail, value)
                        }
                    }
                }

                let n = Node::Node {
                    f: head.clone(),
                    next: Box::new(Vec::new())
                };

                self.roots.push(n);
                self.roots.last_mut().unwrap().add(tail, value)
            },
            None => {
                panic!("leaves are not allowed at the root!")
            }
        }
    }
}

impl<'a> Node<Function, &'a ta::alternating::Clause<u32, Convoluted<u32>>> {
    pub fn to_term(&self, env: &Environment, p: &Rc<Predicate>, function_args: &[smt2::SortedVar<Environment>], mut context_size: usize, variables: &mut Vec<Vec<(usize, Ident)>>) -> smt2::Term<Environment> {
        match self {
            Node::Node { next, .. } => {
                let mut cases = Vec::with_capacity(next.len());
                for n in next.iter() {
                    if let Node::Node { f, .. } = n {
                        let (arity, _) = f.arity(env);
                        let new_variables: Vec<(usize, Ident)> = (0..arity).map(|i| {
                            let index = context_size+i;
                            (index, format!("BOUND_VARIABLE_{}", index).into())
                        }).collect();
                        context_size += arity;

                        let pattern = smt2::Pattern {
                            constructor: f.clone(),
                            args: new_variables.iter().map(|(_, id)| {
                                id.clone()
                            }).collect()
                        };

                        variables.push(new_variables);

                        cases.push(smt2::MatchCase {
                            pattern: pattern,
                            term: Box::new(n.to_term(env, p, function_args, context_size, variables))
                        });

                        variables.pop();
                    } else {
                        return n.to_term(env, p, function_args, context_size, variables);
                    }
                }

                smt2::Term::Match {
                    term: Box::new(smt2::Term::Var { index: 0, id: function_args[0].id.clone() }),
                    cases: cases
                }
            },
            Node::Leaf(clause) => {
                let clause_terms: Vec<_> = clause.iter().map(|conjunction| {
                    let conjunction_terms: Vec<_> = conjunction.iter().map(|(indexes, q)| {
                        let signature = indexes.signature();
                        let mut args = Vec::new();

                        let mut k = 0;
                        for i in indexes.iter() {
                            if let MaybeBottom::Some(i) = i {
                                let (index, id) = variables[k][*i as usize].clone();
                                args.push(smt2::Term::Var {
                                    index: index,
                                    id: id
                                });
                                k += 1;
                            }
                        }

                        smt2::Term::Apply {
                            fun: Function::State(p.clone(), *q, signature),
                            args: Box::new(args),
                            sort: env.sort_bool()
                        }
                    }).collect();

                    if conjunction_terms.is_empty() {
                        smt2::Term::Apply {
                            fun: env.true_fun(),
                            args: Box::new(vec![]),
                            sort: env.sort_bool()
                        }
                    } else {
                        if conjunction_terms.len() == 1 {
                            conjunction_terms.into_iter().next().unwrap()
                        } else {
                            smt2::Term::Apply {
                                fun: Function::And,
                                args: Box::new(conjunction_terms),
                                sort: env.sort_bool()
                            }
                        }
                    }
                }).collect();

                if clause_terms.len() == 1 {
                    clause_terms.into_iter().next().unwrap()
                } else {
                    smt2::Term::Apply {
                        fun: Function::Or,
                        args: Box::new(clause_terms),
                        sort: env.sort_bool()
                    }
                }
            }
        }
    }
}

impl<'a> MatchGraph<Function, &'a ta::alternating::Clause<u32, Convoluted<u32>>> {
    pub fn to_term(&self, env: &Environment, p: &Rc<Predicate>, function_args: &[smt2::SortedVar<Environment>], mut context_size: usize) -> smt2::Term<Environment> {
        let mut variables: Vec<Vec<(usize, Ident)>> = Vec::new();
        let mut cases = Vec::with_capacity(self.roots.len());
        for n in &self.roots {
            if let Node::Node { f, .. } = n {
                let (arity, _) = f.arity(env);
                let new_variables: Vec<(usize, Ident)> = (0..arity).map(|i| {
                    let index = context_size+i;
                    (index, format!("BOUND_VARIABLE_{}", index).into())
                }).collect();
                context_size += arity;

                let pattern = smt2::Pattern {
                    constructor: f.clone(),
                    args: new_variables.iter().map(|(_, id)| {
                        id.clone()
                    }).collect()
                };

                variables.push(new_variables);

                cases.push(smt2::MatchCase {
                    pattern: pattern,
                    term: Box::new(n.to_term(env, p, function_args, context_size, &mut variables))
                });

                variables.pop();
            }
        }

        smt2::Term::Match {
            term: Box::new(smt2::Term::Var { index: 0, id: function_args[0].id.clone() }),
            cases: cases
        }
    }
}
