use std::collections::HashMap;
use std::rc::Rc;
use source_span::Span;
use automatic::{Convoluted, MaybeBottom};
use smt2::Typed;
use crate::{Result, engine};
use super::{
    Environment,
    Predicate,
    Function,
    TypedConstructor,
    MatchGraph
};

impl Environment {
    pub fn produce_model(&self, model: HashMap<Rc<Predicate>, engine::Instance<TypedConstructor>>) -> Result<smt2::response::Model<Self>> {
        let mut definitions = Vec::new();

        for (p, instance) in model.into_iter() {
            let mut declarations = Vec::new();
            let mut bodies = Vec::new();

            let mut initial_functions = Vec::new();

            for q in instance.automaton.states() {
                let mut match_graphs: HashMap<_, MatchGraph<TypedConstructor, &ta::alternating::Clause<u32, Convoluted<u32>>>> = HashMap::new();

                for (convoluted_f, clauses) in instance.automaton.clauses_for_state(q) {
                    let signature = convoluted_f.signature();
                    let mut functions = Vec::new();
                    for f in &convoluted_f.0 {
                        if let MaybeBottom::Some(f) = f {
                            functions.push(f.clone());
                        }
                    }

                    match match_graphs.get_mut(&signature) {
                        Some(match_graph) => {
                            match_graph.add(&functions, clauses);
                        },
                        None => {
                            let mut match_graph = MatchGraph::new();
                            match_graph.add(&functions, clauses);
                            match_graphs.insert(signature, match_graph);
                        }
                    }
                }

                for (signature, match_graph) in &match_graphs {
                    let mut args = Vec::new();
                    let mut indexed_args = Vec::new();
                    let mut s = *signature;
                    let mut full_sig = true;
                    for (i, sort) in p.args.iter().enumerate().rev() {
                        if s & 1 != 0 {
                            let arg = smt2::SortedVar {
                                id: format!("BOUND_VARIABLE_{}", i),
                                sort: sort.clone()
                            };
                            args.push(arg.clone());
                            indexed_args.push((arg, i));
                        } else {
                            full_sig = false;
                        }

                        s >>= 1;
                    }
                    args.reverse();
                    indexed_args.reverse();

                    bodies.push(match_graph.to_term(self, &p, &indexed_args, p.args.len()));

                    let q_fun = Function::State(p.clone(), *q, *signature);

                    if full_sig && instance.automaton.is_initial(q) {
                        initial_functions.push(q_fun.clone());
                    }

                    declarations.push(smt2::response::Declaration {
                        f: q_fun,
                        args: args,
                        return_sort: self.sort_bool.clone()
                    });
                }
            }

            declarations.push(smt2::response::Declaration {
                f: Function::Predicate(p.clone()),
                args: p.args.iter().enumerate().map(|(i, a)| {
                    smt2::SortedVar {
                        id: format!("BOUND_VARIABLE_{}", i),
                        sort: a.clone()
                    }
                }).collect(),
                return_sort: self.sort_bool.clone()
            });

            if initial_functions.len() == 1 {
                let args = p.args.iter().enumerate().map(|(i, a)| Typed::new(smt2::Term::Var {
                    index: i,
                    id: format!("BOUND_VARIABLE_{}", i).into()
                }, Span::default(), a.clone())).collect();

                bodies.push(Typed::new(smt2::Term::Apply {
                    fun: initial_functions.into_iter().next().unwrap(),
                    args: Box::new(args)
                }, Span::default(), self.sort_bool.clone()))
            } else {
                let initial_apps = initial_functions.into_iter().map(|fun| {
                    let args = p.args.iter().enumerate().map(|(i, a)| Typed::new(smt2::Term::Var {
                        index: i,
                        id: format!("BOUND_VARIABLE_{}", i).into()
                    }, Span::default(), a.clone())).collect();

                    Typed::new(smt2::Term::Apply {
                        fun: fun,
                        args: Box::new(args)
                    }, Span::default(), self.sort_bool.clone())
                }).collect();

                bodies.push(Typed::new(smt2::Term::Apply {
                    fun: Function::Or,
                    args: Box::new(initial_apps)
                }, Span::default(), self.sort_bool.clone()))
            }

            definitions.push(smt2::response::Definition {
                rec: true,
                declarations: declarations,
                bodies: bodies,
                comments: if instance.comments.is_empty() {
                    String::new()
                } else {
                    format!("Predicate `{}` internal representation:\n{}", p, instance.comments)
                }
            });
        }

        Ok(smt2::response::Model {
            definitions: definitions
        })
    }
}
