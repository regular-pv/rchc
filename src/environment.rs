use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::cell::RefCell;
use std::borrow::Borrow;
use std::fmt;

use smt2::GroundSort;

use terms::Pattern;

use crate::{Error, Result, rich::*, engine};

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

#[derive(Clone)]
pub struct TypedConstructor {
    /// The term/pattern sort.
    sort: GroundSort<Rc<Sort>>,

    /// The constructor number as indexed in the data-type declaration.
    n: usize
}

impl PartialEq for TypedConstructor {
    fn eq(&self, other: &TypedConstructor) -> bool {
        self.n == other.n && self.sort == other.sort
    }
}

impl Eq for TypedConstructor {}

impl Hash for TypedConstructor {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.n.hash(state);
        self.sort.hash(state)
    }
}

pub struct Sort {
    id: Ident,
    arity: usize,
    def: RefCell<Option<DataTypeDeclaration>>
}

impl Sort {
    pub fn new<Id: Into<Ident>>(id: Id, arity: usize, def: Option<DataTypeDeclaration>) -> Sort {
        Sort {
            id: id.into(),
            arity: arity,
            def: RefCell::new(def)
        }
    }
}

impl PartialEq for Sort {
    fn eq(&self, other: &Sort) -> bool {
        self.def.as_ptr() == other.def.as_ptr()
    }
}

impl Eq for Sort {}

impl Hash for Sort {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.def.as_ptr().hash(state)
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

#[derive(Clone)]
pub enum Function {
    Not,
    And,
    Implies,
    Predicate(Rc<Predicate>),
    Constructor(Rc<Sort>, usize),
}

impl smt2::Function<Environment> for Function {
    fn arity(&self, env: &Environment) -> (usize, usize) {
        match self {
            Function::Not => (1, 1),
            Function::And => (1, std::usize::MAX),
            Function::Implies => (2, 2),
            Function::Predicate(p) => p.arity(env),
            Function::Constructor(sort, n) => {
                let k = sort.def.borrow().as_ref().unwrap().constructors[*n].selectors.len();
                (k, k)
            }
        }
    }

    fn typecheck(&self, env: &Environment, args: &[GroundSort<Rc<Sort>>]) -> std::result::Result<GroundSort<Rc<Sort>>, smt2::TypeCheckError<Rc<Sort>>> {
        use smt2::TypeCheckError::*;
        match self {
            Function::Not => {
                for (i, arg) in args.iter().enumerate() {
                    if *arg != env.sort_bool {
                        return Err(Missmatch(i, (&env.sort_bool).into()))
                    }
                }
                Ok(env.sort_bool.clone())
            },
            Function::And => {
                for (i, arg) in args.iter().enumerate() {
                    if *arg != env.sort_bool {
                        return Err(Missmatch(i, (&env.sort_bool).into()))
                    }
                }
                Ok(env.sort_bool.clone())
            }
            Function::Implies => {
                for (i, arg) in args.iter().enumerate() {
                    if *arg != env.sort_bool {
                        return Err(Missmatch(i, (&env.sort_bool).into()))
                    }
                }
                Ok(env.sort_bool.clone())
            },
            Function::Predicate(p) => p.typecheck(env, args),
            Function::Constructor(sort, n) => {
                let def_option = sort.def.borrow();
                let def = def_option.borrow().as_ref().unwrap();
                let cons = &def.constructors[*n];

                let mut context = Vec::new();
                context.resize(def.parameters.len(), None);

                for (i, arg) in args.iter().enumerate() {
                    let selector = &cons.selectors[i];

                    if let Err(sort) = selector.sort.typecheck(&mut context, arg) {
                        return Err(Missmatch(i, sort))
                    }
                }

                let mut parameters = Vec::with_capacity(context.len());
                for (i, p) in context.drain(..).enumerate() {
                    match p {
                        Some(param) => parameters.push(param),
                        None => return Err(Ambiguity(i))
                    }
                }

                Ok(GroundSort {
                    sort: sort.clone(),
                    parameters: parameters
                })
            }
        }
    }
}

pub struct Predicate {
    args: Vec<GroundSort<Rc<Sort>>>
}

impl PartialEq for Predicate {
    fn eq(&self, other: &Predicate) -> bool {
        self as *const Predicate == other as *const Predicate
    }
}

impl Eq for Predicate {}

impl Hash for Predicate {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self as *const Predicate).hash(state)
    }
}

impl smt2::Function<Environment> for Predicate {
    fn arity(&self, _env: &Environment) -> (usize, usize) {
        (self.args.len(), self.args.len())
    }

    fn typecheck(&self, env: &Environment, args: &[GroundSort<Rc<Sort>>]) -> std::result::Result<GroundSort<Rc<Sort>>, smt2::TypeCheckError<Rc<Sort>>> {
        use smt2::TypeCheckError::*;
        for (i, arg) in args.iter().enumerate() {
            if *arg != self.args[i] {
                return Err(Missmatch(i, (&self.args[i]).into()))
            }
        }
        Ok(env.sort_bool.clone())
    }
}

/// Regular CHC solver environement.
pub struct Environment {
    /// Declared sorts.
    sorts: HashMap<Ident, Rc<Sort>>,

    /// Bool.
    sort_bool: GroundSort<Rc<Sort>>,

    /// Functions.
    functions: HashMap<Ident, Function>,

    /// Engine.
    engine: Box<dyn engine::Abstract<TypedConstructor, Rc<Predicate>>>,
}

impl Environment {
    /// Create a new environment.
    /// At first, only the sort Bool is defined.
    pub fn new<E: 'static + engine::Abstract<TypedConstructor, Rc<Predicate>>>(engine: E) -> Environment {
        let sort_bool = Rc::new(Sort::new("Bool", 0, Some(DataTypeDeclaration {
            parameters: Vec::new(),
            constructors: vec![
                ConstructorDeclaration::simple("True"),
                ConstructorDeclaration::simple("False")
            ]
        })));

        // pre-defined functions.
        let mut functions = HashMap::new();
        functions.insert("not".to_string(), Function::Not);
        functions.insert("and".to_string(), Function::And);
        functions.insert("=>".to_string(), Function::Implies);

        let mut env = Environment {
            sorts: HashMap::new(),
            sort_bool: GroundSort {
                sort: sort_bool.clone(),
                parameters: Vec::new()
            },
            functions: functions,
            engine: Box::new(engine)
        };

        // define Bool.
        env.register_sort(sort_bool);

        env
    }

    /// Register a new sort into the environment.
    pub fn register_sort(&mut self, sort: Rc<Sort>) {
        self.sorts.insert(sort.id.clone(), sort);
    }

    pub fn register_clause(&mut self, clause: Clause<TypedConstructor, Rc<Predicate>>) -> Result<()> {
        Ok(self.engine.assert(clause)?)
    }

    pub fn decode_body(&self, term: &Term) -> Result<Vec<Expr<TypedConstructor, Rc<Predicate>>>> {
        match term {
            smt2::Term::Apply { fun: Function::And, args, .. } => {
                let mut conjuncts = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    conjuncts.push(self.decode_expr(arg)?)
                }
                Ok(conjuncts)
            },
            _ => Ok(vec![self.decode_expr(term)?])
        }
    }

    pub fn decode_expr(&self, term: &Term) -> Result<Expr<TypedConstructor, Rc<Predicate>>> {
        match term {
            smt2::Term::Apply { fun: Function::Predicate(p), args, .. } => {
                let mut patterns = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    patterns.push(self.decode_pattern(arg)?)
                }
                Ok(Expr::Apply(p.clone(), patterns))
            },
            smt2::Term::Var { index, .. } => {
                Ok(Expr::Var(*index))
            },
            _ => Err(Error::InvalidAssertion)
        }
    }

    pub fn decode_pattern(&self, term: &Term) -> Result<Pattern<TypedConstructor, usize>> {
        match term {
            smt2::Term::Var { index, .. } => {
                Ok(Pattern::var(*index))
            },
            smt2::Term::Apply { fun: Function::Constructor(_, n), args, sort } => {
                let f = TypedConstructor {
                    sort: sort.clone(),
                    n: *n
                };

                let mut sub_patterns = Vec::with_capacity(args.len());
                for a in args.iter() {
                    sub_patterns.push(self.decode_pattern(a)?)
                }

                Ok(Pattern::cons(f, sub_patterns))
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
}

impl smt2::Compiler for Environment {
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

    /// Find a function.
    fn function(&self, id: &Ident) -> Option<Function> {
        // match id.as_str() {
        //     "not" => Some(Function::Not),
        //     "and" => Some(Function::And),
        //     "=>" => Some(Function::Implies),
        //     _ => {
        //         match self.predicates.get(id) {
        //             Some(p) => Some(Function::Predicate(p.clone())),
        //             None => None
        //         }
        //     }
        // }
        match self.functions.get(id) {
            Some(f) => Some(f.clone()),
            None => None
        }
    }
}

impl smt2::Server for Environment {
    /// Assert.
    fn assert(&mut self, term: &Term) -> Result<()> {
        // We don't handle every possible assert terms.
        // We need to reject terms that are not HORN clauses,
        // using the "decode" functions.
        use smt2::Term::*;
        match term {
            Forall { body, .. } => {
                match body.borrow() {
                    Apply { fun: Function::Implies, args, .. } => {
                        let body = self.decode_body(&args[0])?;
                        let head = self.decode_expr(&args[1])?;
                        self.register_clause(Clause::new(body, head))?;
                        Ok(())
                    },
                    _ => Err(Error::InvalidAssertion)
                }
            },
            Apply { fun: Function::Not, args, .. } => {
                match args[0].borrow() {
                    Exists { body, .. } => {
                        let body = self.decode_body(&body)?;
                        self.register_clause(Clause::new(body, Expr::False))?;
                        Ok(())
                    },
                    _ => Err(Error::InvalidAssertion)
                }
            },
            term => {
                let head = self.decode_expr(&term)?;
                self.register_clause(Clause::new(Vec::new(), head))?;
                Ok(())
            }
        }
    }

    /// Check satifiability.
    fn check_sat(&mut self) -> Result<smt2::response::CheckSat> {
        use engine::Result::*;
        loop {
            match self.engine.check()? {
                None => return Ok(smt2::response::CheckSat::Sat),
                Some(Sat) => return Ok(smt2::response::CheckSat::Unsat),
                Some(Unknown) => return Ok(smt2::response::CheckSat::Unknown),
                Some(Unsat(new_constraint)) => {
                    for c in new_constraint {
                        self.engine.add(c)?
                    }
                }
            }
        }
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
            def: RefCell::new(None) // undefined.
        }));

        Ok(())
    }

    /// Define the structure of a ADT sort.
    fn define_sort(&mut self, id: &Ident, def: &smt2::DataTypeDeclaration<Self>) -> Result<()> {
        match self.sorts.get(id) {
            Some(sort) => {
                sort.def.replace(Some(def.clone()));
                for (i, cons) in def.constructors.iter().enumerate() {
                    self.functions.insert(cons.id.clone(), Function::Constructor(sort.clone(), i));
                }
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
            self.functions.insert(id.clone(), Function::Predicate(Rc::new(p)));
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
