#![feature(trait_alias)]

#[macro_use]
extern crate log;
extern crate const_vec;
extern crate once_cell;
extern crate smt2;
extern crate terms;
extern crate tree_automata as ta;
extern crate automatic_relations as automatic;
extern crate crossbeam_channel;

pub(crate) mod utils;
mod error;
mod clause;
mod environment;
pub mod teacher;
pub mod learner;
pub mod engine;

pub use error::*;
pub use environment::*;
pub use teacher::Teacher;
pub use learner::{Learner, Model};
pub use engine::Engine;

// pub trait SortedWith<S> {
//	 fn sort(&self) -> &S;
// }
