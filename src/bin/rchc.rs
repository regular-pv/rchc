#[macro_use]
extern crate log;
extern crate stderrlog;
#[macro_use]
extern crate clap;
extern crate utf8_decode;
extern crate source_span;
extern crate smt2;
extern crate rchc;
extern crate automatic_relations as automatic;

use std::io::Read;
use std::rc::Rc;
use utf8_decode::{Decoder, UnsafeDecoder};
use source_span::{
	Position,
	SourceBuffer,
	Metrics,
	DEFAULT_METRICS
};
use smt2::syntax::Parsable;
use automatic::convolution::aligned;

fn main() {
	// Parse options.
	let yaml = load_yaml!("cli.yml");
	let matches = clap::App::from_yaml(yaml).get_matches();

	// Init logger.
	let verbosity = matches.occurrences_of("verbose") as usize;
	stderrlog::new().verbosity(verbosity).init().unwrap();

	let solver = load_smt_solver();

	let teacher = rchc::teacher::Explorer::<aligned::Convolution>::new(read_teacher_options(&matches));
	let learner = match rchc::learner::SMTLearner::<_, _, _, aligned::Convolution>::new(solver) {
		Ok(learner) => learner,
		Err(e) => {
			error!("Unable to load the learner: {}", e);
			std::process::exit(1)
		}
	};

	let engine = rchc::Engine::new(learner, teacher);
	let mut env = rchc::Environment::new(engine);

	if matches.is_present("benchmark") {
		env.enable_benchmark()
	}

	load_asset(&mut env, "builtin", include_bytes!("builtin.smt2"));

	// Choose the input.
	let stdin = std::io::stdin();
	match matches.value_of("INPUT") {
		Some(filename) => {
			info!("reading file: `{}'.", filename);
			match std::fs::File::open(filename) {
				Ok(file) => process_input(&mut env, filename, file),
				Err(e) => {
					error!("unable to open file `{}': {}", filename, e);
					std::process::exit(1)
				}
			}
		},
		None => {
			info!("reading standard input.");
			process_input(&mut env, "stdin".to_string(), stdin.lock())
		}
	}
}

fn load_smt_solver() -> smt2::Client<&'static str, smt2::client::cvc4::Constant, rchc::learner::smt::Sort, rchc::learner::smt::Function<Rc<rchc::Predicate>>> {
	// cvc4 --incremental --finite-model-find --produce-model --lang=smtlib2.6 --output-lang=smtlib2.6
	let mut solver_cmd = std::process::Command::new("cvc4");
	solver_cmd.args(&["--incremental", "--finite-model-find", "--produce-model", "--lang=smtlib2.6", "--output-lang=smtlib2.6"]);
	match smt2::Client::<_, smt2::client::cvc4::Constant, _, _>::new(
		solver_cmd,
		rchc::learner::smt::Sort::Bool,
		rchc::learner::smt::Function::True,
		rchc::learner::smt::Function::False
	) {
		Ok(solver) => solver,
		Err(e) => {
			error!("Unable to load SMT-solver: {}", e);
			std::process::exit(1)
		}
	}
}

fn read_teacher_options(matches: &clap::ArgMatches) -> rchc::teacher::Options {
	let mut options = rchc::teacher::Options::default();
	options.learn_fast = matches.is_present("learn-fast");
	if let Some(value) = matches.value_of("max-states") {
		if let Ok(value) = usize::from_str_radix(value.as_ref(), 10) {
			options.max_states = value;
		} else {
			warn!("option ignored: invalid integer `{}`", value)
		}
	}
	options
}

fn load_asset(env: &mut rchc::Environment, name: &str, data: &[u8]) {
	let start = Position::default();
	let decoder = Decoder::new(data.iter().cloned());
	let buffer = SourceBuffer::new(decoder, start, DEFAULT_METRICS);
	process_buffer(env, name, buffer, start, &DEFAULT_METRICS)
}

/// Process a given SMT2-lib input.
fn process_input<Input: Read, F: std::fmt::Display + Clone>(env: &mut rchc::Environment, file: F, input: Input) {
	let start = Position::default();
	let decoder = UnsafeDecoder::new(input.bytes());
	let buffer = SourceBuffer::new(decoder, start, DEFAULT_METRICS);
	process_buffer(env, file, buffer, start, &DEFAULT_METRICS)
}

fn process_buffer<I: Iterator<Item = std::io::Result<char>>, F: std::fmt::Display + Clone, M: Metrics + Clone>(env: &mut rchc::Environment, file: F, buffer: SourceBuffer<std::io::Error, I, M>, start: Position, metrics: &M) {
	let mut lexer = smt2::Lexer::new(buffer.iter(), start, metrics.clone()).peekable();

	// read command until end of file.
	while let Some(_) = lexer.peek() {
		match smt2::syntax::Command::parse(&mut lexer) {
			Ok(phrase) => {
				match smt2::compile(env, &phrase) {
					Ok(cmd) => {
						match cmd.exec(env) {
							Ok(()) => (),
							Err(e) => {
								let viewport = phrase.span().aligned();
								smt2::error::Infos::print_at(&e, file, &buffer, viewport, phrase.span(), metrics).unwrap();
								std::process::exit(1)
							}
						}
					},
					Err(e) => {
						let viewport = phrase.span().aligned();
						smt2::error::Infos::print(e, file, &buffer, viewport, metrics).unwrap();
						std::process::exit(1)
					}
				}
			},
			Err(e) => {
				let viewport = e.span().aligned().inter(buffer.span());
				smt2::error::Infos::print(e, file, &buffer, viewport, metrics).unwrap();
				std::process::exit(1)
			}
		}
	}
}
