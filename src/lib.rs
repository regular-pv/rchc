#[macro_use]
extern crate log;
extern crate smt2;
extern crate tree_automata as ta;

use std::collections::HashMap;
use std::rc::Rc;
use std::cell::Cell;
use std::borrow::Borrow;
use std::fmt;

use smt2::GroundSort;

pub mod teacher;
pub mod learner;

pub use teacher::Teacher;
pub use learner::Learner;

/// Runtime errors.
pub enum Error {
    /// For non-HORN assertions.
    InvalidAssertion
}

type Result = smt2::ExecResult<Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            InvalidAssertion => write!(f, "invalid assertion")
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Logic {
    /// HORN logic.
    /// This is the only logic supported by this solver.
    HORN
}

pub type Ident = String;

type DataTypeDeclaration = smt2::DataTypeDeclaration<Environment>;
type ConstructorDeclaration = smt2::ConstructorDeclaration<Environment>;
type Term = smt2::Term<Environment>;

pub struct Sort {
    id: Ident,
    arity: usize,
    def: Cell<Option<DataTypeDeclaration>>
}

impl Sort {
    pub fn new<Id: Into<Ident>>(id: Id, arity: usize, def: Option<DataTypeDeclaration>) -> Sort {
        Sort {
            id: id.into(),
            arity: arity,
            def: Cell::new(def)
        }
    }
}

impl PartialEq for Sort {
    fn eq(&self, other: &Sort) -> bool {
        self.def.as_ptr() == other.def.as_ptr()
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

pub enum Function {
    Not,
    Implies
}

impl smt2::Function<Environment> for Function {
    fn arity(&self, _env: &Environment) -> usize {
        match self {
            Function::Not => 1,
            Function::Implies => 2
        }
    }

    fn sort(&self, env: &Environment, index: usize) -> Option<GroundSort<Rc<Sort>>> {
        match self {
            Function::Not => {
                match index {
                    0 => Some(env.sort_bool.clone()),
                    _ => None
                }
            },
            Function::Implies => {
                match index {
                    0 => Some(env.sort_bool.clone()),
                    1 => Some(env.sort_bool.clone()),
                    _ => None
                }
            }
        }
    }

    fn result(&self, env: &Environment) -> GroundSort<Rc<Sort>> {
        // all our functions must return a Bool.
        env.sort_bool.clone()
    }
}

/// Regular CHC solver environement.
pub struct Environment {
    /// Declared sorts.
    sorts: HashMap<Ident, Rc<Sort>>,

    /// Bool.
    sort_bool: GroundSort<Rc<Sort>>
}

impl Environment {
    /// Create a new environment.
    /// At first, only the sort Bool is defined.
    pub fn new() -> Environment {
        let sort_bool = Rc::new(Sort::new("Bool", 0, Some(DataTypeDeclaration {
            parameters: Vec::new(),
            constructors: vec![
                ConstructorDeclaration::simple("True"),
                ConstructorDeclaration::simple("False")
            ]
        })));

        let mut env = Environment {
            sorts: HashMap::new(),
            sort_bool: GroundSort {
                sort: sort_bool.clone(),
                parameters: Vec::new()
            }
        };

        // define Bool.
        env.register_sort(sort_bool);

        env
    }

    /// Register a new sort into the environment.
    pub fn register_sort(&mut self, sort: Rc<Sort>) {
        self.sorts.insert(sort.id.clone(), sort);
    }
}

impl smt2::Environment for Environment {
    type Logic = Logic;
    type Ident = Ident;
    type Sort = Rc<Sort>;
    type Function = Function;
    type Error = Error;

    /// Find the ident for the iven syntax symbol.
    fn ident_of_symbol<F: Clone>(&self, sym: &smt2::syntax::Symbol<F>) -> Option<Ident> {
        Some(sym.id.clone())
    }

    /// Find the ident for the given syntax ident.
    fn ident<F: Clone>(&self, id: &smt2::syntax::Ident<F>) -> Option<Ident> {
        if id.indexes.is_empty() {
            self.ident_of_symbol(&id.id)
        } else {
            None
        }
    }

    /// Find the logic with the given id.
    fn logic(&self, id: &Ident) -> Option<Logic> {
        if id == "HORN" {
            Some(Logic::HORN)
        } else {
            None
        }
    }

    /// Find a sort.
    fn sort(&self, id: &Ident) -> Option<Rc<Sort>> {
        match self.sorts.get(id) {
            Some(sort) => Some(sort.clone()),
            None => None
        }
    }

    /// The Bool sort.
    fn sort_bool(&self) -> GroundSort<Rc<Sort>> {
        self.sort_bool.clone()
    }

    /// Find a function.
    fn function(&self, id: &Ident) -> Option<Function> {
        match id.as_str() {
            "not" => Some(Function::Not),
            "=>" => Some(Function::Implies),
            _ => None
        }
    }

    /// Assert.
    fn assert(&mut self, term: &Term) -> Result {
        use smt2::Term::*;
        match term {
            Forall { vars, body } => {
                match body.borrow() {
                    Apply { fun: Function::Implies, args } => {
                        let body = &args[0];
                        let head = &args[1];
                        Ok(())
                    },
                    _ => Err(Error::InvalidAssertion)
                }
            },
            Apply { fun: Function::Not, args } => {
                Err(Error::InvalidAssertion)
            },
            _ => Err(Error::InvalidAssertion)
        }
    }

    /// Check satifiability.
    fn check_sat(&mut self) -> Result {
        Ok(())
    }

    /// Declare a new constant.
    fn declare_const(&mut self, id: &Ident, sort: &GroundSort<Rc<Sort>>) -> Result {
        Ok(())
    }

    /// Declare a new sort.
    /// The sort starts undefined, so it cannot be used before [`define_sort`] is called to
    /// define the structure of the ADT.
    fn declare_sort(&mut self, decl: &smt2::SortDeclaration<Self>) -> Result {
        self.register_sort(Rc::new(Sort {
            id: decl.id.clone(),
            arity: decl.arity,
            def: Cell::new(None) // undefined.
        }));

        Ok(())
    }

    /// Define the structure of a ADT sort.
    fn define_sort(&mut self, id: &Ident, def: &smt2::DataTypeDeclaration<Self>) -> Result {
        match self.sorts.get(id) {
            Some(sort) => {
                sort.def.set(Some(def.clone()))
            },
            None => {
                panic!("sort is undefined")
            }
        }

        Ok(())
    }

    /// Declare new function.
    fn declare_fun(&mut self, id: &Ident, args: &Vec<GroundSort<Rc<Sort>>>, return_sort: &GroundSort<Rc<Sort>>) -> Result {
        Ok(())
    }

    /// Exit the solver.
    fn exit(&mut self) -> Result {
        std::process::exit(0);
        Ok(())
    }

    /// Set the solver's logic.
    fn set_logic(&mut self, logic: &Self::Logic) -> Result {
        // doesn't have to do anything since the only logic we know is HORN.
        match logic {
            Logic::HORN => Ok(())
        }
    }
}
