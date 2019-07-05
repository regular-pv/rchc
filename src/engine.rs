use std::marker::PhantomData;
use std::fmt;
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

pub trait Abstract<F: Clone, P: Clone> {
    /// Add a new clause to the solver.
    fn assert(&mut self, clause: rich::Clause<F, P>) -> std::result::Result<(), Error>;

    /// Find the next model and check it.
    fn check(&mut self) -> std::result::Result<Option<Result<F, P>>, Error>;

    /// Add a learning constraint.
    fn add(&mut self, new_constraint: Constraint<F, P>) -> std::result::Result<(), Error>;
}

pub struct Engine<F: Clone, P: Clone, I, L, T, M> where M: Model<P, I>, L: Learner<F, P, I, Model=M>, T: Teacher<F, P, I, Model=M> {
    learner: L,
    teacher: T,
    _f: PhantomData<F>,
    _p: PhantomData<P>,
    _i: PhantomData<I>,
    _m: PhantomData<M>
}

impl<F: Clone, P: Clone, I, L, T, M> Engine<F, P, I, L, T, M> where M: Model<P, I>, L: Learner<F, P, I, Model=M>, T: Teacher<F, P, I, Model=M> {
    pub fn new(learner: L, teacher: T) -> Engine<F, P, I, L, T, M> {
        Engine {
            learner: learner,
            teacher: teacher,
            _f: PhantomData,
            _p: PhantomData,
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

impl<F: Clone, P: Clone, I, L, T, M> Abstract<F, P> for Engine<F, P, I, L, T, M> where M: Model<P, I>, L: Learner<F, P, I, Model=M>, T: Teacher<F, P, I, Model=M> {
    /// Add a new clause to the solver.
    fn assert(&mut self, clause: rich::Clause<F, P>) -> std::result::Result<(), Error> {
        Self::teacher_result(self.teacher.assert(clause))
    }

    /// Find the next model and check it.
    fn check(&mut self) -> std::result::Result<Option<Result<F, P>>, Error> {
        match Self::learner_result(self.learner.produce_model())? {
            Some(model) => Ok(Some(Self::teacher_result(self.teacher.check(&model))?)),
            None => Ok(None)
        }
    }

    /// Add a learning constraint.
    fn add(&mut self, new_constraint: Constraint<F, P>) -> std::result::Result<(), Error> {
        Self::learner_result(self.learner.add(new_constraint))
    }
}
