# Regular CHC Solver

A regular CHC solver written in Rust.
It can read and check SMT2-LIB files containing regular problems.

## Installation

### Nightly Rust

This program uses some unstable features of Rust that can only be found in the nightly build.
You can install it through [`rustup`](https://rustup.rs/) with the following command:
```
$ rustup install nightly
```

### Running

First, close this repository using:
```
$ git clone git@github.com:regular-pv/rchc.git
```

You can then install `rchc` locally using:
```
$ cargo +nightly install --path .
```
The binary is, by default, installed in `$HOME/.cargo/bin`.
You may want to check that it is in your `$PATH`.

If you don't want to install `rchc`, you can still run it
from the closed repository using cargo:
```
$ cargo +nightly run --
```
Every argument given after `--` is passed to `rchc`.

## Usage

You can see all the options using ``$ rchc --help``. Most of the time,
you will only use it like this:

```
$ rchc file.smt2
```

### Input format

The input file is expected to be in the standard [SMT2-lib format](http://smtlib.cs.uiowa.edu/).
The typical input looks like this:
```
(set-logic HORN)

(declare-fun ...)
...

(assert ...)
...

(check-sat)
(get-model)
```

The `(set-logic HORN)` sets the logic to the only one supported,
`HORN`.
The constraint system defined with the `assert` commands must
represent a constrained Horn clauses system.
It doesn't have to be specified in the canonical form,
but be aware that `rchc` will not always be smart enough to translate the input into a CHC system if it is not obvious enough.
For now, all the declared functions (with `declare-fun`) must be relations (functions with output type `Bool`).

### Output format

The `(get-model)` command, which can only be called after `(check-sat)` returns `sat`,
will output an instantiation of the declared relations.
Internally, relations are represented using tree automata which can makes the output hard to read.
It may be easier to directly read the automaton representation of the relation which is
outputted as comments before the relation definition.

### Examples

Some problem examples can be found in the `examples` folder.

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
