use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::cell::UnsafeCell;
use std::sync::{Arc, RwLock};
use std::borrow::Borrow;
use std::fmt;

use smt2::GroundSort;
use terms::Pattern;
use ta::{
    bottom_up::{
        Automaton,
        Configuration
    },
    NoLabel,
    Ranked,
    Rank,
    SortedWith
};
use automatic::{Convoluted, MaybeBottom, convolution::aligned};

use crate::{Error, Result, rich::*, engine};

mod match_graph;
mod produce_model;

pub use match_graph::*;

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

#[derive(Clone, Debug)]
pub struct TypedConstructor {
    /// The term/pattern sort.
    sort: GroundSort<Arc<Sort>>,

    /// The constructor number as indexed in the data-type declaration.
    n: usize,

    // arity of the constructor
    arity: usize
}

impl SortedWith<GroundSort<Arc<Sort>>> for TypedConstructor {
    fn sort(&self) -> &GroundSort<Arc<Sort>> {
        &self.sort
    }
}

impl Ranked for TypedConstructor {
    fn arity(&self) -> usize {
        self.arity
    }
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

impl fmt::Display for TypedConstructor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let guard = self.sort.sort.def.read().unwrap();
        if let Some(def) = &*guard {
            if let Some(cons) = def.constructors.get(self.n) {
                write!(f, "{}", cons.id)
            } else {
                write!(f, "{}.{}!", self.sort, self.n)
            }
        } else {
            write!(f, "{}.{}", self.sort, self.n)
        }
    }
}

pub type ConvolutedSort = Convoluted<GroundSort<Arc<crate::Sort>>>;

pub struct GroundSortConfigurations {
    gsort: GroundSort<Arc<Sort>>,
    current_constructor: usize
}

impl GroundSortConfigurations {
    pub fn new(gsort: &GroundSort<Arc<Sort>>) -> GroundSortConfigurations {
        GroundSortConfigurations {
            gsort: gsort.clone(),
            current_constructor: 0
        }
    }
}

impl Iterator for GroundSortConfigurations {
    type Item = Configuration<TypedConstructor, GroundSort<Arc<Sort>>>;

    fn next(&mut self) -> Option<Self::Item> {
        let i = self.current_constructor;
        match &*self.gsort.sort.def.read().unwrap() {
            Some(def) => {
                if let Some(constructor) = def.constructors.get(i) {
                    self.current_constructor += 1;
                    let f = TypedConstructor {
                        sort: self.gsort.clone(),
                        n: i,
                        arity: constructor.selectors.len()
                    };

                    let mut states = Vec::with_capacity(f.arity);
                    for sel in &constructor.selectors {
                        match sel.sort.instanciate(&self.gsort.parameters) {
                            Ok(gsort) => states.push(gsort),
                            Err(_) => panic!("malformed ground sort!")
                        }
                    }

                    Some(Configuration(f, states))
                } else {
                    None
                }
            },
            None => None
        }
    }
}

impl ta::bottom_up::LanguageState<TypedConstructor, ()> for GroundSort<Arc<Sort>> {
    fn configurations<'a>(&self, _env: &'a ()) -> Box<dyn Iterator<Item = Configuration<TypedConstructor, Self>> + 'a> {
        Box::new(GroundSortConfigurations::new(self))
    }
}

pub struct Sort {
    id: Ident,
    //arity: usize,
    def: RwLock<Option<DataTypeDeclaration>>
}

impl Sort {
    pub fn new<Id: Into<Ident>>(id: Id, _arity: usize, def: Option<DataTypeDeclaration>) -> Arc<Sort> {
        Arc::new(Sort {
            id: id.into(),
            //arity: arity,
            def: RwLock::new(def)
        })
    }
}

impl PartialEq for Sort {
    fn eq(&self, other: &Sort) -> bool {
        self as *const Sort == other as *const Sort
    }
}

impl Eq for Sort {}

impl Hash for Sort {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self as *const Sort).hash(state)
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Function {
    Not,
    And,
    Or,
    Implies,
    Predicate(Rc<Predicate>),
    Constructor(Arc<Sort>, usize),
    State(Rc<Predicate>, u32, u32)
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Function::*;
        match self {
            Not => write!(f, "not"),
            And => write!(f, "and"),
            Or => write!(f, "or"),
            Implies => write!(f, "=>"),
            Predicate(p) => write!(f, "{}", p),
            Constructor(sort, n) => {
                let guard = sort.def.read().unwrap();
                if let Some(def) = &*guard {
                    if let Some(cons) = def.constructors.get(*n) {
                        write!(f, "{}", cons.id)
                    } else {
                        write!(f, "{}.{}!", sort, n)
                    }
                } else {
                    write!(f, "{}.{}", sort, n)
                }
            },
            State(p, q, sig) => write!(f, "@q_{}_{}_{}", p, q, sig),
        }
    }
}

impl smt2::Function<Environment> for Function {
    fn arity(&self, env: &Environment) -> (usize, usize) {
        match self {
            Function::Not => (1, 1),
            Function::And | Function::Or => (1, std::usize::MAX),
            Function::Implies => (2, 2),
            Function::Predicate(p) => p.arity(env),
            Function::Constructor(sort, n) => {
                let def = sort.def.read().unwrap();
                let k = def.as_ref().unwrap().constructors[*n].selectors.len();
                (k, k)
            },
            Function::State(p, _, _) => p.arity(env)
        }
    }

    fn typecheck(&self, env: &Environment, args: &[GroundSort<Arc<Sort>>]) -> std::result::Result<GroundSort<Arc<Sort>>, smt2::TypeCheckError<Arc<Sort>>> {
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
            Function::And | Function::Or => {
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
                let def_option = sort.def.read().unwrap();
                let def = def_option.as_ref().unwrap();
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
            },
            _ => {
                unreachable!()
            }
        }
    }
}

struct PredicateData {
    domain: Automaton<Rank<Convoluted<TypedConstructor>>, ConvolutedSort, NoLabel>,
    alphabet: HashSet<Rank<Convoluted<TypedConstructor>>>
}

pub struct Predicate {
    id: Ident,
    args: Vec<GroundSort<Arc<Sort>>>,
    data: UnsafeCell<Option<PredicateData>>
}

impl Predicate {
    fn data(&self) -> &PredicateData {
        let data = unsafe { &mut *self.data.get() };
        match data {
            Some(data) => data,
            None => {
                let convoluted_sort = Convoluted(self.args.iter().map(|sort| MaybeBottom::Some(sort.clone())).collect());
                let domain = aligned::automaton::state_convolution(convoluted_sort, &());
                let alphabet = domain.alphabet();
                *data = Some(PredicateData {
                    domain: domain,
                    alphabet: alphabet
                });
                data.as_ref().unwrap()
            }
        }
    }

    pub fn domain(&self) -> &Automaton<Rank<Convoluted<TypedConstructor>>, ConvolutedSort, NoLabel> {
        &self.data().domain
    }

    pub fn alphabet(&self) -> &HashSet<Rank<Convoluted<TypedConstructor>>> {
        &self.data().alphabet
    }
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

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}

impl smt2::Function<Environment> for Predicate {
    fn arity(&self, _env: &Environment) -> (usize, usize) {
        (self.args.len(), self.args.len())
    }

    fn typecheck(&self, env: &Environment, args: &[GroundSort<Arc<Sort>>]) -> std::result::Result<GroundSort<Arc<Sort>>, smt2::TypeCheckError<Arc<Sort>>> {
        use smt2::TypeCheckError::*;
        for (i, arg) in args.iter().enumerate() {
            if *arg != self.args[i] {
                return Err(Missmatch(i, (&self.args[i]).into()))
            }
        }
        Ok(env.sort_bool.clone())
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Constant {
    // no constants.
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "@constant")
    }
}

/// Regular CHC solver environement.
pub struct Environment {
    /// Declared sorts.
    sorts: HashMap<Ident, Arc<Sort>>,

    /// Bool.
    sort_bool: GroundSort<Arc<Sort>>,

    /// Functions.
    functions: HashMap<Ident, Function>,

    /// Engine.
    engine: Box<dyn engine::Abstract<TypedConstructor, Rc<Predicate>>>,
}

impl Environment {
    /// Create a new environment.
    /// At first, only the sort Bool is defined.
    pub fn new<E: 'static + engine::Abstract<TypedConstructor, Rc<Predicate>>>(engine: E) -> Environment {
        let sort_bool = Sort::new("Bool", 0, Some(DataTypeDeclaration {
            parameters: Vec::new(),
            constructors: vec![
                ConstructorDeclaration::simple("true"),
                ConstructorDeclaration::simple("false")
            ]
        }));

        // pre-defined functions.
        let mut functions = HashMap::new();
        functions.insert("not".to_string(), Function::Not);
        functions.insert("and".to_string(), Function::And);
        functions.insert("or".to_string(), Function::Or);
        functions.insert("=>".to_string(), Function::Implies);
        functions.insert("true".to_string(), Function::Constructor(sort_bool.clone(), 0));
        functions.insert("false".to_string(), Function::Constructor(sort_bool.clone(), 1));

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

    pub fn true_fun(&self) -> Function {
        Function::Constructor(self.sort_bool.sort.clone(), 0)
    }

    pub fn false_fun(&self) -> Function {
        Function::Constructor(self.sort_bool.sort.clone(), 1)
    }

    /// Register a new sort into the environment.
    pub fn register_sort(&mut self, sort: Arc<Sort>) {
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
                let def = sort.sort.def.read().unwrap();
                let arity = def.as_ref().unwrap().constructors[*n].selectors.len();
                let f = TypedConstructor {
                    sort: sort.clone(),
                    n: *n,
                    arity: arity
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
    type Constant = Constant;
    type Sort = Arc<Sort>;
    type Function = Function;
    type Error = Error;

    /// Find a sort.
    fn sort(&self, id: &Ident) -> Option<Arc<Sort>> {
        match self.sorts.get(id) {
            Some(sort) => Some(sort.clone()),
            None => None
        }
    }

    /// The Bool sort.
    fn sort_bool(&self) -> GroundSort<Arc<Sort>> {
        self.sort_bool.clone()
    }

    fn const_sort(&self, _cst: &Constant) -> GroundSort<Arc<Sort>> {
        panic!("TODO const_sort")
    }
}

impl smt2::Compiler for Environment {
    /// Find the ident for the iven syntax symbol.
    fn ident_of_symbol(&self, sym: &smt2::syntax::Symbol) -> Option<Ident> {
        Some(sym.id.clone())
    }

    /// Find the ident for the given syntax ident.
    fn ident(&self, id: &smt2::syntax::Ident) -> Option<Ident> {
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

    fn constant(&self, _id: &Ident) -> Option<Constant> {
        None
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
                    Apply { fun: Function::Not, args, .. } => {
                        let body = self.decode_body(&args[0])?;
                        let head = Expr::False;
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
                None => return Ok(smt2::response::CheckSat::Unsat),
                Some(Sat) => return Ok(smt2::response::CheckSat::Sat),
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
    fn declare_const(&mut self, _id: &Ident, _sort: &GroundSort<Arc<Sort>>) -> Result<()> {
        Ok(())
    }

    /// Declare a new sort.
    /// The sort starts undefined, so it cannot be used before [`define_sort`] is called to
    /// define the structure of the ADT.
    fn declare_sort(&mut self, decl: &smt2::SortDeclaration<Self>) -> Result<()> {
        self.register_sort(Arc::new(Sort {
            id: decl.id.clone(),
            //arity: decl.arity,
            def: RwLock::new(None) // undefined.
        }));

        Ok(())
    }

    /// Define the structure of a ADT sort.
    fn define_sort(&mut self, id: &Ident, def: &smt2::DataTypeDeclaration<Self>) -> Result<()> {
        match self.sorts.get(id) {
            Some(sort) => {
                let mut sort_def = sort.def.write().unwrap();
                *sort_def = Some(def.clone());
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
    fn declare_fun(&mut self, id: &Ident, args: &Vec<GroundSort<Arc<Sort>>>, return_sort: &GroundSort<Arc<Sort>>) -> Result<()> {
        if *return_sort != self.sort_bool {
            Err(Error::InvalidPredicateReturnType)
        } else {
            let p = Rc::new(Predicate {
                id: id.clone(),
                args: args.clone(),
                data: UnsafeCell::new(None)
            });
            self.functions.insert(id.clone(), Function::Predicate(p.clone()));
            self.engine.declare_predicate(p)?;
            Ok(())
        }
    }

    /// Exit the solver.
    fn exit(&mut self) -> Result<()> {
        std::process::exit(0);
    }

    fn get_model(&mut self) -> Result<smt2::response::Model<Self>> {
        if let Some(model) = self.engine.produce_model() {
            self.produce_model(model)
        } else {
            Err(Error::NoModel)
        }
    }

    /// Set the solver's logic.
    fn set_logic(&mut self, logic: &Self::Logic) -> Result<()> {
        // doesn't have to do anything since the only logic we know is HORN.
        match logic {
            Logic::HORN => Ok(())
        }
    }
}
