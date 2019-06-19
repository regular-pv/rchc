#[macro_use]
extern crate log;
extern crate stderrlog;
#[macro_use]
extern crate clap;

extern crate smt2;
extern crate rchc;

use std::io::Read;
use smt2::syntax::{Localisable, Buffer};
use smt2::syntax::Parsable;

fn main() {
    // Parse options.
	let yaml = load_yaml!("cli.yml");
    let matches = clap::App::from_yaml(yaml).get_matches();

    // Init logger.
	let verbosity = matches.occurrences_of("verbose") as usize;
    stderrlog::new().verbosity(verbosity).init().unwrap();

	let teacher = Box::new(rchc::teacher::Explorer::new());
	let mut env = rchc::Environment::new(teacher);

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

/// Process a given SMT2-lib input.
fn process_input<Input: Read, F: std::fmt::Display + Clone>(env: &mut rchc::Environment, input: Input, file: F) {
	let start = smt2::syntax::Cursor::default();
	let decoder = smt2::lexer::Decoder::new(input.bytes());
	let buffer = Buffer::new(decoder, start);
	let mut lexer = smt2::Lexer::new(buffer.reader(), file.clone(), start).peekable();

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
								println!("\x1b[1;34m  -->\x1b[m {}", phrase.location());
								let mut pp = smt2::syntax::PrettyPrinter::new(&buffer, phrase.location());
								pp.add_hint(phrase.location());
								println!("{}", pp);
							}
						}
					},
					Err(e) => {
						println!("\x1b[1;31merror\x1b[m\x1b[1;1m: {}\x1b[m", e);
						println!("\x1b[1;34m  -->\x1b[m {}", e.location());
						let mut pp = smt2::syntax::PrettyPrinter::new(&buffer, phrase.location());
						pp.add_hint(e.location());
						println!("{}", pp);
					}
				}
			},
			Err(e) => {
				println!("\x1b[1;31mparse error\x1b[m\x1b[1;1m: {}\x1b[m", e);
				println!("\x1b[1;34m  -->\x1b[m {}", e.location());
				let mut pp = smt2::syntax::PrettyPrinter::new(&buffer, e.location());
				pp.add_hint(e.location());
				println!("{}", pp);

				std::process::exit(1)
			}
		}
	}
}
