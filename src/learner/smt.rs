use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::sync::Arc;
use std::marker::PhantomData;
use std::fmt;
use terms::Term;
use ta::{
	NoLabel,
	Symbol,
	Rank,
	SortedWith,
	bottom_up::{Automaton, Configuration}
};
use automatic::{Convolution, Convoluted, MaybeBottom};
use smt2::{Typed, Sorted, Environment, client::{FunctionSignature, Constant}, GroundSort};
use crate::{ConvolutedSort};
use crate::teacher::explorer::Relation;

use super::{Learner, Constraint, Sample};

pub type Result<T, K, P> = std::result::Result<T, Error<K, P>>;

pub enum Error<K: Clone + PartialEq, P: Predicate> {
	Solver(SolverError<K, P>),
	// Unsat,
	Unknown
}

impl<K: Clone + PartialEq, P: Predicate> From<SolverError<K, P>> for Error<K, P> {
	fn from(e: SolverError<K, P>) -> Error<K, P> {
		Error::Solver(e)
	}
}

impl<K: Clone + PartialEq, P: Predicate> fmt::Display for Error<K, P> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Error::Solver(e) => write!(f, "SMT-solver: {}", e),
			// Error::Unsat => write!(f, "SMT-solver response to (check-sat) was `unsat`"),
			Error::Unknown => write!(f, "SMT-solver response to (check-sat) was `unknown`")
		}
	}
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Function<P: Predicate> {
	True,
	False,
	Eq,
	Not,
	And,
	Or,
	Implies,
	Ite,
	Q(ConvolutedSort, u32),
	Predicate(P)
}

impl<P: Predicate + fmt::Display> fmt::Display for Function<P> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Function::True => write!(f, "true"),
			Function::False => write!(f, "false"),
			Function::Eq => write!(f, "="),
			Function::Not => write!(f, "not"),
			Function::And => write!(f, "and"),
			Function::Or => write!(f, "or"),
			Function::Implies => write!(f, "=>"),
			Function::Ite => write!(f, "ite"),
			Function::Q(sort, i) => write!(f, "q{}:{}", i, sort),
			Function::Predicate(p) => write!(f, "p{}", p)
		}
	}
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sort {
	Bool,
	Q
}

impl smt2::client::Sort for Sort {
	fn arity(&self) -> usize {
		0
	}
}

impl fmt::Display for Sort {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Sort::Bool => write!(f, "Bool"),
			Sort::Q => write!(f, "Q")
		}
	}
}

pub type Solver<K, P> = smt2::Client<&'static str, K, Sort, Function<P>>;
pub type SolverError<K, P> = smt2::client::Error<&'static str, K, Sort, Function<P>>;

pub struct PredicateData<F: Symbol> {
	automaton: Automaton<Rank<Convoluted<F>>, AbsQ, NoLabel>,
	domain: ConvolutedSort
}

pub struct SMTLearner<K: Clone + PartialEq, F: Symbol, P: Predicate, C: Convolution<F>> {
	predicates: Vec<PredicateData<F>>,
	solver: Solver<K, P>,
	namespace: Namespace,
	const_sort: smt2::GroundSort<Sort>,
	predicate_ids: HashMap<P, u32>,
	unsat: bool,
	c: PhantomData<C>
}

/// States of the abstract automaton.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AbsQ(ConvolutedSort, u32);

impl fmt::Display for AbsQ {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "q{}:{}", self.1, self.0)
	}
}

pub type Q = crate::teacher::explorer::Q;

impl AbsQ {
	pub fn as_fun<P: Predicate>(&self) -> Function<P> {
		Function::Q(self.0.clone(), self.1)
	}
}

pub struct Namespace {
	count: u32
}

impl Namespace {
	pub fn new() -> Namespace {
		Namespace {
			count: 0
		}
	}

	pub fn spawn(&mut self, sort: ConvolutedSort) -> AbsQ {
		let id = self.count;
		self.count += 1;
		AbsQ(sort, id)
	}
}

impl<K: Constant + fmt::Display, F: Constructor, P: Predicate, C: Convolution<F>> SMTLearner<K, F, P, C> {
	pub fn new(mut solver: Solver<K, P>) -> Result<SMTLearner<K, F, P, C>, K, P> {
		let const_sort = smt2::GroundSort::new(Sort::Q);
		solver.declare_sort(Sort::Q)?;
		solver.predefined_fun("=", Function::Eq, FunctionSignature::Equality)?;
		solver.predefined_fun("not", Function::Not, FunctionSignature::LogicUnary)?;
		solver.predefined_fun("and", Function::And, FunctionSignature::LogicNary)?;
		solver.predefined_fun("or", Function::Or, FunctionSignature::LogicNary)?;
		solver.predefined_fun("=>", Function::Implies, FunctionSignature::LogicBinary)?;
		solver.predefined_fun("ite", Function::Ite, FunctionSignature::Ite)?;
		Ok(SMTLearner {
			predicates: Vec::new(),
			namespace: Namespace::new(),
			solver: solver,
			const_sort: const_sort,
			predicate_ids: HashMap::new(),
			unsat: false,
			c: PhantomData
		})
	}

	fn predicate_id(&self, predicate: &P) -> u32 {
		*self.predicate_ids.get(predicate).unwrap()
	}

	fn op(&self, op: Function<P>, args: Vec<Typed<smt2::Term<Solver<K, P>>>>) -> Typed<smt2::Term<Solver<K, P>>> {
		smt2::Term::apply(op, args, self.solver.sort_bool())
	}

	fn as_term(&self, q: &AbsQ) -> Typed<smt2::Term<Solver<K, P>>> {
		smt2::Term::apply(q.as_fun(), Vec::new(), self.const_sort.clone())
	}

	fn declare_transition(&mut self, predicate: u32, Configuration(f, states): &Configuration<Rank<Convoluted<F>>, AbsQ>, q: AbsQ) -> Result<(), K, P> {
		for (Configuration(other_f, other_states), _, other_q) in self.predicates[predicate as usize].automaton.transitions() {
			if f == other_f {
				let mut clause = vec![self.op(Function::Eq, vec![self.as_term(&q), self.as_term(other_q)])];
				for (i, sub_state) in states.iter().enumerate() {
					let other_sub_state = other_states[i].clone();
					clause.push(self.op(Function::Not, vec![self.op(Function::Eq, vec![self.as_term(sub_state), self.as_term(&other_sub_state)])]));
				}

				let term = self.op(Function::Or, clause);
				self.solver.assert(&term)?
			}
		}

		Ok(())
	}

	fn add_term(&mut self, predicate: u32, term: Term<Rank<Convoluted<F>>>) -> Result<AbsQ, K, P> {
		let namespace = &mut self.namespace;
		let mut new_transitons = Vec::new();
		let term_q = self.predicates[predicate as usize].automaton.add_normalized(&term, &mut |configuration| {
			let convoluted_f = configuration.symbol();
			let mut conv_sort = Vec::with_capacity(convoluted_f.0.len());
			for f in convoluted_f.0.iter() {
				let sort = match f {
					MaybeBottom::Bottom => MaybeBottom::Bottom,
					MaybeBottom::Some(f) => MaybeBottom::Some(f.sort().clone())
				};
				conv_sort.push(sort);
			}

			let q = namespace.spawn(Convoluted(conv_sort));
			new_transitons.push((configuration.clone(), q.clone()));
			(q, NoLabel)
		});

		for (_, q) in &new_transitons {
			self.solver.declare_const(q.as_fun(), &self.const_sort)?;
		}

		for (configuration, q) in new_transitons.into_iter() {
			self.declare_transition(predicate, &configuration, q)?
		}

		Ok(term_q)
	}

	fn add_sample(&mut self, Sample(predicate, _, term): Sample<P, F>) -> Result<AbsQ, K, P> {
		self.add_term(self.predicate_id(&predicate), term)
	}

	fn application_term(&self, p: &P, positive: bool, q: &AbsQ) -> Typed<smt2::Term<Solver<K, P>>> {
		if positive {
			self.op(Function::Predicate(p.clone()), vec![self.as_term(q)])
		} else {
			self.op(Function::Not, vec![self.op(Function::Predicate(p.clone()), vec![self.as_term(&q)])])
		}
	}

	fn assert_positive(&mut self, p: P, positive: bool, q: AbsQ) -> Result<(), K, P> {
		self.solver.assert(&self.application_term(&p, positive, &q))?;
		Ok(())
	}

	fn assert_negative(&mut self, states: &[(P, bool, AbsQ)]) -> Result<(), K, P> {
		self.solver.assert(&self.op(Function::Not, vec![
			self.op(Function::And, states.iter().map(|(p, pos, q)| {
				self.application_term(p, *pos, q)
			}).collect())
		]))?;
		Ok(())
	}

	fn assert_implication(&mut self, lhs: &[(P, bool, AbsQ)], rhs: (P, bool, AbsQ)) -> Result<(), K, P> {
		match lhs.len() {
			0 => {
				self.solver.assert(&self.application_term(&rhs.0, rhs.1, &rhs.2))?;
			},
			1 => {
				let (p, pos, q) = &lhs[0];
				self.solver.assert(&self.op(Function::Implies, vec![
					self.application_term(p, *pos, q),
					self.application_term(&rhs.0, rhs.1, &rhs.2)
				]))?;
			},
			_ => {
				self.solver.assert(&self.op(Function::Implies, vec![
					self.op(Function::And, lhs.iter().map(|(p, pos, q)| {
						self.application_term(p, *pos, q)
					}).collect()),
					self.application_term(&rhs.0, rhs.1, &rhs.2)
				]))?;
			}
		}
		Ok(())
	}

	fn is_final_state(state: u32, term: &Typed<smt2::Term<Solver<K, P>>>) -> bool {
		#[derive(PartialEq)]
		enum Value {
			Q(u32),
			Bool(bool)
		}

		fn eval<K: Constant, P: Predicate>(state: u32, term: &Typed<smt2::Term<Solver<K, P>>>) -> Value {
			match term.as_ref() {
				smt2::Term::Var { .. } => Value::Q(state),
				smt2::Term::Const(Sorted(cst, _)) => {
					Value::Q(cst.index())
				},
				smt2::Term::Apply { fun: Function::True, .. } => {
					Value::Bool(true)
				},
				smt2::Term::Apply { fun: Function::False, .. } => {
					Value::Bool(false)
				},
				smt2::Term::Apply { fun: Function::Eq, args, .. } => {
					Value::Bool(eval(state, &args[0]) == eval(state, &args[1]))
				},
				smt2::Term::Apply { fun: Function::Ite, args, .. } => {
					if eval(state, &args[0]) == Value::Bool(true) {
						eval(state, &args[1])
					} else {
						eval(state, &args[2])
					}
				},
				_ => panic!("invalid state definition term! It may also be unsupported.")
			}
		}

		eval(state, term) == Value::Bool(true)
	}
}

/// Learner trait.
impl<K: Constant + fmt::Display, F: Constructor, P: Predicate, C: Convolution<F>> Learner<F, P, Relation<F, Q, C>> for SMTLearner<K, F, P, C> {
	type Model = HashMap<P, Relation<F, Q, C>>;
	type Error = Error<K, P>;

	/// Declare a new predicate to learn.
	fn declare_predicate(&mut self, p: P, domain: ConvolutedSort) -> Result<(), K, P> {
		let index = self.predicates.len() as u32;
		self.predicate_ids.insert(p.clone(), index);
		self.predicates.push(PredicateData {
			automaton: Automaton::new(),
			domain: domain
		});

		Ok(self.solver.declare_fun(Function::Predicate(p), &vec![self.const_sort.clone()], &self.solver.sort_bool())?)
	}

	/// Add a learning constraint.
	fn add(&mut self, new_constraint: Constraint<F, P>) -> Result<(), K, P> {
		// debug!("add constraint: {:?}", new_constraint);

		match new_constraint {
			Constraint::Positive(sample) => {
				let p = sample.0.clone();
				let pos = sample.1;
				let q = self.add_sample(sample)?;
				self.assert_positive(p, pos, q)
			},
			Constraint::Negative(mut samples) => {
				let mut states = Vec::with_capacity(samples.len());
				for s in samples.drain(..) {
					let p = s.0.clone();
					let pos = s.1;
					states.push((p, pos, self.add_sample(s)?))
				}
				self.assert_negative(&states)
			},
			Constraint::Implication(lhs, rhs) => {
				let mut lhs_states = Vec::with_capacity(lhs.len());
				for s in lhs.into_iter() {
					let p = s.0.clone();
					let pos = s.1;
					lhs_states.push((p, pos, self.add_sample(s)?))
				}
				let rhs_p = rhs.0.clone();
				let rhs_pos = rhs.1;
				let rhs_state = self.add_sample(rhs)?;
				self.assert_implication(&lhs_states, (rhs_p, rhs_pos, rhs_state))
			},
			Constraint::False => {
				self.unsat = true;
				Ok(())
			}
		}
	}

	/// Produce a model that respects all the constraints given to the learner.
	fn produce_model(&mut self) -> Result<Option<Self::Model>, K, P> {
		if self.unsat {
			Ok(None)
		} else {
			match self.solver.check_sat()? {
				smt2::response::CheckSat::Sat => {
					let smt_model = self.solver.get_model()?;
					let mut model = HashMap::new();

					let mut table = HashMap::new();
					let mut predicates_defs: Vec<(P, Typed<smt2::Term<Solver<K, P>>>)> = Vec::new();

					for mut def in smt_model.definitions.into_iter() {
						def.bodies.reverse();
						for decl in def.declarations.into_iter() {
							let body = def.bodies.pop().unwrap();
							match decl.f {
								Function::Q(_, i) => {
									match body.into_inner() {
										smt2::Term::Const(Sorted(c, _)) => {
											table.insert(i, c.index());
										},
										_ => panic!("unexpected state definition!")
									}
								},
								Function::Predicate(p) => {
									predicates_defs.push((p.clone(), body));
								},
								_ => ()
							}
						}
					}

					for (p, body) in &predicates_defs {
						let i = self.predicate_id(p) as usize;
						let data = &self.predicates[i];
						let abs_aut = &data.automaton;
						// println!("-----------");
						// println!("abs_aut: {}", abs_aut);
						//let mut final_states = HashSet::new();
						let mut aut = abs_aut.map_states(|AbsQ(sort, k)| {
							Q::Alive(sort.clone(), *table.get(k).unwrap())
						});

						let mut final_states = HashSet::new();
						for q in aut.states() {
							if let Q::Alive(sort, k) = q {
								if *sort == data.domain && Self::is_final_state(*k, body) {
									final_states.insert(q.clone());
								}
							}
						}

						for q in final_states.into_iter() {
							aut.set_final(q);
						}

						// println!("aut: {}", aut);
						// println!("-----------");

						model.insert(p.clone(), Relation(aut, PhantomData));
					}

					Ok(Some(model))
				},
				smt2::response::CheckSat::Unsat => {
					self.unsat = true;
					Ok(None)
				},
				smt2::response::CheckSat::Unknown => Err(Error::Unknown)
			}
		}
	}
}

pub trait Predicate = Clone + Eq + Hash + fmt::Display + fmt::Debug;
pub trait Constructor = Symbol + Eq + Hash + SortedWith<GroundSort<Arc<crate::Sort>>> + fmt::Debug;
