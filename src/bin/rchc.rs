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
use utf8_decode::UnsafeDecoder;
use source_span::{
	Position,
	lazy::Buffer,
	fmt::*
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

	let teacher = rchc::teacher::Explorer::<aligned::Convolution>::new();

	let learner = match rchc::learner::SMTLearner::<_, _, _, aligned::Convolution>::new(solver) {
		Ok(learner) => learner,
		Err(e) => {
			error!("Unable to load the learner: {}", e);
			std::process::exit(1)
		}
	};

	let engine = rchc::Engine::new(learner, teacher);
	let mut env = rchc::Environment::new(engine);

    // Choose the input.
    let stdin = std::io::stdin();
    match matches.value_of("INPUT") {
        Some(filename) => {
            info!("reading file: `{}'.", filename);
            match std::fs::File::open(filename) {
                Ok(file) => process_input(&mut env, file, filename),
                Err(e) => {
                    error!("unable to open file `{}': {}", filename, e);
                    std::process::exit(1)
                }
            }
        },
        None => {
            info!("reading standard input.");
            process_input(&mut env, stdin.lock(), "stdin".to_string())
        }
    }
}

fn load_smt_solver() -> smt2::Client<&'static str, smt2::client::cvc4::Constant, rchc::learner::smt::Sort, rchc::learner::smt::Function<Rc<rchc::Predicate>>> {
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

/// Process a given SMT2-lib input.
fn process_input<Input: Read, F: std::fmt::Display + Clone>(env: &mut rchc::Environment, input: Input, file: F) {
	let start = Position::default();
	let decoder = UnsafeDecoder::new(input.bytes());
	let buffer = Buffer::new(decoder, start);
	let mut lexer = smt2::Lexer::new(buffer.iter(), start).peekable();

	// read command until end of file.
	while let Some(_) = lexer.peek() {
		match smt2::syntax::Command::parse(&mut lexer) {
			Ok(phrase) => {
				match smt2::compile(env, &phrase) {
					Ok(cmd) => {
						match cmd.exec(env) {
							Ok(()) => (),
							Err(e) => {
								println!("\x1b[1;31mruntime error\x1b[m\x1b[1;1m: {}\x1b[m", e);
								println!("\x1b[1;34m  -->\x1b[m {} {}", file, phrase.span());
								let mut pp = Formatter::new();
								pp.add(phrase.span(), None, Style::Error);

								let viewport = phrase.span().aligned();
								println!("{}", pp.get(buffer.iter_from(viewport.start()), viewport).unwrap());

								std::process::exit(1)
							}
						}
					},
					Err(e) => {
						println!("\x1b[1;31merror\x1b[m\x1b[1;1m: {}\x1b[m", e);
						println!("\x1b[1;34m  -->\x1b[m {} {}", file, e.span());
						let mut pp = Formatter::new();

						use smt2::Error::*;
						let label = match e.as_ref() {
							TypeAmbiguity => Some(format!("use the `(as {} <sort>)` type coercion construct to remove the ambiguity", buffer.iter_span(e.span()).into_string().unwrap())),
							_ => None
						};

						pp.add(e.span(), label, Style::Error);

						let viewport = phrase.span().aligned();
						println!("{}", pp.get(buffer.iter_from(viewport.start()), viewport).unwrap());

						std::process::exit(1)
					}
				}
			},
			Err(e) => {
				println!("\x1b[1;31mparse error\x1b[m\x1b[1;1m: {}\x1b[m", e);
				println!("\x1b[1;34m  -->\x1b[m {} {}", file, e.span());
				let mut pp = Formatter::new();
				pp.add(e.span(), None, Style::Error);

				let viewport = e.span().aligned().inter(buffer.span());
				let formatted = pp.get(buffer.iter_from(viewport.start()), viewport).unwrap();
				print!("{}", formatted);

				std::process::exit(1)
			}
		}
	}
}
