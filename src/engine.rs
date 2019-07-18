use std::marker::PhantomData;
use std::fmt;
use std::collections::HashMap;
use std::hash::Hash;
use automatic::Convoluted;
use ta::Symbol;
use crate::{Learner, Teacher, Model, rich};
use crate::learner::{Sample, Constraint};
pub use crate::teacher::Result;

pub enum Error {
    Learner(String),
    Teacher(String)
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            Learner(msg) => write!(f, "learner: {}", msg),
            Teacher(msg) => write!(f, "teacher: {}", msg)
        }
    }
}

pub type Instance<F> = ta::alternating::Automaton<Convoluted<F>, u32, Convoluted<u32>>;

pub trait ToInstance<F: Symbol> {
    fn to_instance(&self) -> Instance<F>;
}

pub trait Abstract<F: Symbol, P: Clone> {
    /// Declare a new predicate to solve.
    fn declare_predicate(&mut self, p: P) -> std::result::Result<(), Error>;

    /// Add a new clause to the solver.
    fn assert(&mut self, clause: rich::Clause<F, P>) -> std::result::Result<(), Error>;

    /// Find the next model and check it.
    fn check(&mut self) -> std::result::Result<Option<Result<F, P>>, Error>;

    /// Add a learning constraint.
    fn add(&mut self, new_constraint: Constraint<F, P>) -> std::result::Result<(), Error>;

    /// Produce model.
    fn produce_model(&self) -> Option<HashMap<P, Instance<F>>>;
}

pub struct Engine<F: Symbol, P: Clone, I, L, T, M> where M: Model<P, I>, L: Learner<F, P, I, Model=M>, T: Teacher<F, P, I, Model=M> {
    learner: L,
    teacher: T,
    predicates: Vec<P>,
    model: Option<L::Model>,
    _f: PhantomData<F>,
    _i: PhantomData<I>,
    _m: PhantomData<M>
}

impl<F: Symbol, P: Clone, I, L, T, M> Engine<F, P, I, L, T, M> where M: Model<P, I>, L: Learner<F, P, I, Model=M>, T: Teacher<F, P, I, Model=M> {
    pub fn new(learner: L, teacher: T) -> Engine<F, P, I, L, T, M> {
        Engine {
            learner: learner,
            teacher: teacher,
            predicates: Vec::new(),
            model: None,
            _f: PhantomData,
            _i: PhantomData,
            _m: PhantomData
        }
    }

    fn teacher_result<D>(r: std::result::Result<D, T::Error>) -> std::result::Result<D, Error> {
        match r {
            Ok(t) => Ok(t),
            Err(e) => {
                let message = format!("{}", e);
                Err(Error::Teacher(message))
            }
        }
    }

    fn learner_result<D>(r: std::result::Result<D, L::Error>) -> std::result::Result<D, Error> {
        match r {
            Ok(t) => Ok(t),
            Err(e) => {
                let message = format!("{}", e);
                Err(Error::Learner(message))
            }
        }
    }
}

impl<F: Symbol, P: Clone + Eq + Hash, I: ToInstance<F>, L, T, M> Abstract<F, P> for Engine<F, P, I, L, T, M> where M: Model<P, I>, L: Learner<F, P, I, Model=M>, T: Teacher<F, P, I, Model=M>, P: fmt::Display, I: fmt::Display {
    /// Declare a new predicate to solve.
    fn declare_predicate(&mut self, p: P) -> std::result::Result<(), Error> {
        self.predicates.push(p.clone());
        Self::learner_result(self.learner.declare_predicate(p))
    }

    /// Add a new clause to the solver.
    fn assert(&mut self, clause: rich::Clause<F, P>) -> std::result::Result<(), Error> {
        Self::teacher_result(self.teacher.assert(clause))
    }

    /// Find the next model and check it.
    fn check(&mut self) -> std::result::Result<Option<Result<F, P>>, Error> {
        self.model = Self::learner_result(self.learner.produce_model())?;
        match &self.model {
            Some(model) => Ok(Some(Self::teacher_result(self.teacher.check(model))?)),
            None => Ok(None)
        }
    }

    /// Add a learning constraint.
    fn add(&mut self, new_constraint: Constraint<F, P>) -> std::result::Result<(), Error> {
        Self::learner_result(self.learner.add(new_constraint))
    }

    fn produce_model(&self) -> Option<HashMap<P, Instance<F>>> {
        if let Some(model) = &self.model {
            let mut map = HashMap::new();
            for p in &self.predicates {
                map.insert(p.clone(), model.get(p).to_instance());
            }

            Some(map)
        } else {
            None
        }
    }
}
