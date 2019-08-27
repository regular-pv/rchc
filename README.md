# Regular CHC Solver

A regular CHC solver written in Rust.
It can read and check SMT2-LIB files containing regular problems.

## Installation

```
$ git clone git@github.com:regular-pv/rchc.git
$ cargo install --path .
```

The binary is, by default, installed in `$HOME/.cargo/bin`.
You may want to check that it is in your `$PATH`.

## Usage

You can see all the options using ``$ rchc --help``. Most of the time,
you will only use it like this:

```
$ rchc file.smt2
```

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
