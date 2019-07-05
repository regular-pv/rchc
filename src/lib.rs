#[macro_use]
extern crate log;
extern crate smt2;
extern crate terms;
extern crate tree_automata as ta;
extern crate automatic_relations as automatic;

mod error;
mod clause;
mod environment;
pub mod teacher;
pub mod learner;
pub mod engine;

pub use error::*;
pub use clause::*;
pub use environment::*;
pub use teacher::Teacher;
pub use learner::{Learner, Model};
pub use engine::Engine;
