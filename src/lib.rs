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
    InvalidAssertion,

    /// For non-Bool predicates.
    InvalidPredicateReturnType
}

type Result<T> = smt2::ExecResult<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            InvalidAssertion => write!(f, "invalid assertion"),
            InvalidPredicateReturnType => write!(f, "invalid predicate return type")
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
    And,
    Implies,
    Predicate(Rc<Predicate>)
}

impl smt2::Function<Environment> for Function {
    fn arity(&self, env: &Environment) -> (usize, usize) {
        match self {
            Function::Not => (1, 1),
            Function::And => (1, std::usize::MAX),
            Function::Implies => (2, 2),
            Function::Predicate(p) => p.arity(env)
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
            Function::And => {
                match index {
                    _ => Some(env.sort_bool.clone())
                }
            }
            Function::Implies => {
                match index {
                    0 => Some(env.sort_bool.clone()),
                    1 => Some(env.sort_bool.clone()),
                    _ => None
                }
            },
            Function::Predicate(p) => p.sort(env, index)
        }
    }

    fn result(&self, env: &Environment) -> GroundSort<Rc<Sort>> {
        // all our functions must return a Bool.
        env.sort_bool.clone()
    }
}

pub struct Predicate {
    args: Vec<GroundSort<Rc<Sort>>>
}

impl smt2::Function<Environment> for Predicate {
    fn arity(&self, _env: &Environment) -> (usize, usize) {
        (self.args.len(), self.args.len())
    }

    fn sort(&self, _env: &Environment, index: usize) -> Option<GroundSort<Rc<Sort>>> {
        match self.args.get(index) {
            Some(sort) => Some(sort.clone()),
            None => None
        }
    }

    fn result(&self, env: &Environment) -> GroundSort<Rc<Sort>> {
        // it's a predicate. So it returns Bool.
        env.sort_bool.clone()
    }
}

pub enum Atom {
    False,
    Var(usize)
}

pub enum Expr {
    Apply(Rc<Predicate>, Vec<Atom>),
    Atom(Atom)
}

/// Horn clause.
pub struct Clause {
    body: Vec<Expr>,
    head: Expr
}

impl Clause {
    pub fn new(body: Vec<Expr>, head: Expr) -> Clause {
        Clause {
            body: body,
            head: head
        }
    }
}

/// Regular CHC solver environement.
pub struct Environment {
    /// Declared sorts.
    sorts: HashMap<Ident, Rc<Sort>>,

    /// Bool.
    sort_bool: GroundSort<Rc<Sort>>,

    /// Predicates.
    predicates: HashMap<Ident, Rc<Predicate>>,

    /// Teacher.
    teacher: Box<Teacher>,
}

impl Environment {
    /// Create a new environment.
    /// At first, only the sort Bool is defined.
    pub fn new(teacher: Box<Teacher>) -> Environment {
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
            },
            predicates: HashMap::new(),
            teacher: teacher
        };

        // define Bool.
        env.register_sort(sort_bool);

        env
    }

    /// Register a new sort into the environment.
    pub fn register_sort(&mut self, sort: Rc<Sort>) {
        self.sorts.insert(sort.id.clone(), sort);
    }

    pub fn register_clause(&mut self, clause: Clause) {
        self.teacher.assert(clause)
    }

    pub fn decode_body(&self, term: &Term) -> Result<Vec<Expr>> {
        match term {
            smt2::Term::Apply { fun: Function::And, args } => {
                let mut conjuncts = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    conjuncts.push(self.decode_expr(arg)?)
                }
                Ok(conjuncts)
            },
            _ => Ok(vec![self.decode_expr(term)?])
        }
    }

    pub fn decode_expr(&self, term: &Term) -> Result<Expr> {
        match term {
            smt2::Term::Apply { fun: Function::Predicate(p), args } => {
                let mut atoms = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    atoms.push(self.decode_atom(arg)?)
                }
                Ok(Expr::Apply(p.clone(), atoms))
            },
            _ => Ok(Expr::Atom(self.decode_atom(term)?))
        }
    }

    pub fn decode_atom(&self, term: &Term) -> Result<Atom> {
        match term {
            smt2::Term::Var { index, .. } => {
                Ok(Atom::Var(*index))
            },
            _ => Err(Error::InvalidAssertion)
        }
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
            "and" => Some(Function::And),
            "=>" => Some(Function::Implies),
            _ => {
                match self.predicates.get(id) {
                    Some(p) => Some(Function::Predicate(p.clone())),
                    None => None
                }
            }
        }
    }

    /// Assert.
    fn assert(&mut self, term: &Term) -> Result<()> {
        use smt2::Term::*;
        match term {
            Forall { body, .. } => {
                match body.borrow() {
                    Apply { fun: Function::Implies, args } => {
                        let body = self.decode_body(&args[0])?;
                        let head = self.decode_expr(&args[1])?;
                        self.register_clause(Clause::new(body, head));
                        Ok(())
                    },
                    _ => Err(Error::InvalidAssertion)
                }
            },
            Apply { fun: Function::Not, args } => {
                match args[0].borrow() {
                    Exists { body, .. } => {
                        let body = self.decode_body(&body)?;
                        self.register_clause(Clause::new(body, Expr::Atom(Atom::False)));
                        Ok(())
                    },
                    _ => Err(Error::InvalidAssertion)
                }
            },
            _ => Err(Error::InvalidAssertion)
        }
    }

    /// Check satifiability.
    fn check_sat(&mut self) -> Result<()> {
        Ok(())
    }

    /// Declare a new constant.
    fn declare_const(&mut self, _id: &Ident, _sort: &GroundSort<Rc<Sort>>) -> Result<()> {
        Ok(())
    }

    /// Declare a new sort.
    /// The sort starts undefined, so it cannot be used before [`define_sort`] is called to
    /// define the structure of the ADT.
    fn declare_sort(&mut self, decl: &smt2::SortDeclaration<Self>) -> Result<()> {
        self.register_sort(Rc::new(Sort {
            id: decl.id.clone(),
            arity: decl.arity,
            def: Cell::new(None) // undefined.
        }));

        Ok(())
    }

    /// Define the structure of a ADT sort.
    fn define_sort(&mut self, id: &Ident, def: &smt2::DataTypeDeclaration<Self>) -> Result<()> {
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
    fn declare_fun(&mut self, id: &Ident, args: &Vec<GroundSort<Rc<Sort>>>, return_sort: &GroundSort<Rc<Sort>>) -> Result<()> {
        if *return_sort != self.sort_bool {
            Err(Error::InvalidPredicateReturnType)
        } else {
            let p = Predicate {
                args: args.clone()
            };
            self.predicates.insert(id.clone(), Rc::new(p));
            Ok(())
        }
    }

    /// Exit the solver.
    fn exit(&mut self) -> Result<()> {
        std::process::exit(0);
    }

    /// Set the solver's logic.
    fn set_logic(&mut self, logic: &Self::Logic) -> Result<()> {
        // doesn't have to do anything since the only logic we know is HORN.
        match logic {
            Logic::HORN => Ok(())
        }
    }
}
