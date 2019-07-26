use std::rc::Rc;
use std::sync::Arc;
use source_span::Span;
use smt2::Environment as SMT2Environment;
use smt2::{Typed, GroundSort};
use ta::Ranked;
use automatic::MaybeBottom;
use super::{Environment, Predicate, Sort, TypedConstructor, Function, Ident, Convoluted};

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

impl<'a> Node<TypedConstructor, &'a ta::alternating::Clause<u32, Convoluted<u32>>> {
    pub fn to_term(&self, env: &Environment, p: &Rc<Predicate>, function_args: &[(smt2::SortedVar<Environment>, usize)], k: usize, mut context_size: usize, variables: &mut Vec<Vec<(usize, GroundSort<Arc<Sort>>, Ident)>>) -> Typed<smt2::Term<Environment>> {
        match self {
            Node::Node { next, .. } => {
                let mut cases = Vec::with_capacity(next.len());
                for n in next.iter() {
                    if let Node::Node { f, .. } = n {
                        let arity = f.arity();
                        let new_variables: Vec<(usize, GroundSort<Arc<Sort>>, Ident)> = (0..arity).map(|i| {
                            let index = context_size+i;
                            let sort = f.parameter(i);
                            (index, sort, format!("BOUND_VARIABLE_{}", index).into())
                        }).collect();
                        context_size += arity;

                        let sort = function_args[k].0.sort.clone();
                        let pattern = smt2::Pattern::Cons {
                            constructor: Function::Constructor(f.sort.sort.clone(), f.n),
                            args: new_variables.iter().map(|(_, _, id)| {
                                id.clone()
                            }).collect()
                        };

                        variables.push(new_variables);

                        let pattern_sort = function_args[k].0.sort.clone();

                        cases.push(smt2::MatchCase {
                            pattern: Typed::new(pattern, Span::default(), pattern_sort.clone()),
                            term: Box::new(n.to_term(env, p, function_args, k+1, context_size, variables))
                        });

                        variables.pop();
                    } else {
                        return n.to_term(env, p, function_args, k, context_size, variables);
                    }
                }

                let sort = function_args[k].0.sort.clone();

                {
                    let arg_def = p.args[k].sort.def.read().unwrap();
                    let len = arg_def.as_ref().unwrap().constructors.len();

                    if cases.len() < len {
                        cases.push(smt2::MatchCase {
                            pattern: Typed::new(smt2::Pattern::Var("_".into()), Span::default(), sort.clone()),
                            term: Box::new(Typed::new(smt2::Term::Apply {
                                fun: env.false_fun(),
                                args: Box::new(vec![])
                            }, Span::default(), env.sort_bool()))
                        });
                    }
                }

                Typed::new(smt2::Term::Match {
                    term: Box::new(Typed::new(smt2::Term::Var { index: k, id: function_args[k].0.id.clone()}, Span::default(), sort)),
                    cases: cases
                }, Span::default(), env.sort_bool())
            },
            Node::Leaf(clause) => {
                let clause_terms: Vec<_> = clause.iter().map(|conjunction| {
                    let conjunction_terms: Vec<_> = conjunction.iter().map(|(indexes, q)| {
                        let signature = indexes.signature();
                        let mut args = Vec::new();

                        let mut k = 0;
                        for (i, index) in indexes.iter().enumerate() {
                            if let MaybeBottom::Some(index) = index {
                                assert!(k < variables.len());
                                assert!((*index as usize) < variables[k].len());
                                let (x, sort, id) = variables[k][*index as usize].clone();
                                args.push(Typed::new(smt2::Term::Var {
                                    index: x,
                                    id: id
                                }, Span::default(), sort));
                            }

                            if function_args[k].1 == i {
                                k += 1;
                            }
                        }

                        Typed::new(smt2::Term::Apply {
                            fun: Function::State(p.clone(), *q, signature),
                            args: Box::new(args)
                        }, Span::default(), env.sort_bool())
                    }).collect();

                    if conjunction_terms.is_empty() {
                        Typed::new(smt2::Term::Apply {
                            fun: env.true_fun(),
                            args: Box::new(vec![]),
                        }, Span::default(), env.sort_bool())
                    } else {
                        if conjunction_terms.len() == 1 {
                            conjunction_terms.into_iter().next().unwrap()
                        } else {
                            Typed::new(smt2::Term::Apply {
                                fun: Function::And,
                                args: Box::new(conjunction_terms),
                            }, Span::default(), env.sort_bool())
                        }
                    }
                }).collect();

                if clause_terms.len() == 1 {
                    clause_terms.into_iter().next().unwrap()
                } else {
                    Typed::new(smt2::Term::Apply {
                        fun: Function::Or,
                        args: Box::new(clause_terms)
                    }, Span::default(), env.sort_bool())
                }
            }
        }
    }
}

impl<'a> MatchGraph<TypedConstructor, &'a ta::alternating::Clause<u32, Convoluted<u32>>> {
    pub fn to_term(&self, env: &Environment, p: &Rc<Predicate>, function_args: &[(smt2::SortedVar<Environment>, usize)], mut context_size: usize) -> Typed<smt2::Term<Environment>> {
        let sort = function_args[0].0.sort.clone();
        let mut variables: Vec<Vec<(usize, GroundSort<Arc<Sort>>, Ident)>> = Vec::new();
        let mut cases = Vec::with_capacity(self.roots.len());
        for n in &self.roots {
            if let Node::Node { f, .. } = n {
                let arity = f.arity();
                let new_variables: Vec<(usize, GroundSort<Arc<Sort>>, Ident)> = (0..arity).map(|i| {
                    let index = context_size+i;
                    let sort = f.parameter(i);
                    (index, sort, format!("BOUND_VARIABLE_{}", index).into())
                }).collect();
                context_size += arity;

                let pattern = Typed::new(smt2::Pattern::Cons {
                    constructor: Function::Constructor(f.sort.sort.clone(), f.n),
                    args: new_variables.iter().map(|(_, _, id)| {
                        id.clone()
                    }).collect()
                }, Span::default(), sort.clone());

                variables.push(new_variables);

                cases.push(smt2::MatchCase {
                    pattern: pattern,
                    term: Box::new(n.to_term(env, p, function_args, 1, context_size, &mut variables))
                });

                variables.pop();
            }
        }

        {
            let arg_def = p.args[0].sort.def.read().unwrap();
            let len = arg_def.as_ref().unwrap().constructors.len();

            if cases.len() < len {
                cases.push(smt2::MatchCase {
                    pattern: Typed::new(smt2::Pattern::Var("_".into()), Span::default(), sort.clone()),
                    term: Box::new(Typed::new(smt2::Term::Apply {
                        fun: env.false_fun(),
                        args: Box::new(vec![])
                    }, Span::default(), env.sort_bool()))
                });
            }
        }

        Typed::new(smt2::Term::Match {
            term: Box::new(Typed::new(smt2::Term::Var { index: 0, id: function_args[0].0.id.clone() }, Span::default(), sort)),
            cases: cases
        }, Span::default(), env.sort_bool())
    }
}
