use terms::Term;

pub enum Atom<F> {
    Term(Term<F>),
    Var(usize)
}

pub enum Expr<F, P> {
    True,
    False,
    Apply(P, Vec<Atom<F>>)
}

/// Horn clause.
pub struct Clause<F, P> {
    body: Vec<Expr<F, P>>,
    head: Expr<F, P>
}

impl<F, P> Clause<F, P> {
    pub fn new(body: Vec<Expr<F, P>>, head: Expr<F, P>) -> Clause<F, P> {
        Clause {
            body: body,
            head: head
        }
    }
}

pub mod rich {
    use crate::clause as simplified;
    use terms::Pattern;

    pub enum Expr<F: Clone, P: Clone> {
        True,
        False,
        Var(usize),
        Apply(P, Vec<Pattern<F, usize>>)
    }

    impl<F: Clone, P: Clone> Expr<F, P> {
        fn max_indice(&self) -> usize {
            match self {
                Expr::Var(x) => x+1,
                Expr::Apply(_, patterns) => {
                    let mut max = 0;
                    for pattern in patterns.iter() {
                        for x in pattern.variables() {
                            if *x >= max {
                                max = x+1
                            }
                        }
                    }
                    max
                },
                Expr::True => 0,
                Expr::False => 0
            }
        }

        fn simplify<G>(&self, x: &mut usize, predicate_gen: &G) -> (simplified::Expr<F, P>, Vec<simplified::Expr<F, P>>) where G: Fn(&Pattern<F, usize>) -> P {
            match self {
                Expr::Var(_) => {
                    panic!("TODO simplify var expr.")
                },
                Expr::Apply(p, patterns) => {
                    let mut atoms = Vec::with_capacity(patterns.len());
                    let mut fresh = Vec::new();
                    for pattern in patterns.iter() {
                        match pattern.as_term() {
                            Some(term) => {
                                atoms.push(simplified::Atom::Term(term))
                            },
                            None => {
                                let fresh_x = *x;
                                *x += 1;

                                let new_predicate = (*predicate_gen)(&pattern.reindex());
                                let mut args = vec![simplified::Atom::Var(fresh_x)];
                                let mut indexes: Vec<usize> = pattern.variables().map(|x| x.clone()).collect();
                                indexes.sort();
                                for i in indexes {
                                    args.push(simplified::Atom::Var(i))
                                }

                                fresh.push(simplified::Expr::Apply(new_predicate, args));
                                atoms.push(simplified::Atom::Var(fresh_x));
                            }
                        }
                    }

                    (simplified::Expr::Apply(p.clone(), atoms), fresh)
                },
                Expr::True => (simplified::Expr::True, Vec::new()),
                Expr::False => (simplified::Expr::False, Vec::new())
            }
        }
    }

    pub struct Clause<F: Clone, P: Clone> {
        body: Vec<Expr<F, P>>,
        head: Expr<F, P>
    }

    impl<F: Clone, P: Clone> Clause<F, P> {
        pub fn new(body: Vec<Expr<F, P>>, head: Expr<F, P>) -> Clause<F, P> {
            Clause {
                body: body,
                head: head
            }
        }

        /// The arity of a clause is defined as the number of variables occuring in the clause.
        /// In our case, since we use De Bruijn indices we just need to take the maximum indice
        /// (if we consider the indices starts at 1).
        pub fn arity(&self) -> usize {
            let mut max = self.head.max_indice();
            for e in self.body.iter() {
                max = std::cmp::max(max, e.max_indice());
            }

            max
        }

        /// Simpliy the clause to remove patterns.
        /// In the resulting simple clause, patterns are replaced by fresh variables and terms
        /// a preserved.
        /// New predicates may be introduced to preserve the semantics of the clause using the
        /// given function.
        pub fn simplify<G>(&self, predicate_gen: &G) -> simplified::Clause<F, P> where G: Fn(&Pattern<F, usize>) -> P {
            // A fresh variable. We use the arity to make sure to use a fresh name.
            let mut x = self.arity();
            let mut simplified_body = Vec::with_capacity(self.body.len());
            for e in self.body.iter() {
                let (simplified, mut fresh) = e.simplify(&mut x, predicate_gen);
                simplified_body.push(simplified);
                simplified_body.append(&mut fresh);
            }

            let (simplified_head, mut fresh) = self.head.simplify(&mut x, predicate_gen);
            simplified_body.append(&mut fresh);

            simplified::Clause::new(simplified_body, simplified_head)
        }

        /// Try to align the variables in the clause to simplify it.
        pub fn align(&self) -> simplified::Clause<F, P> {
            panic!("TODO align")
        }
    }
}
