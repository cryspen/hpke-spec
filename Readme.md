# HPKE Specification

This repository contains an annotated and executable version of the [HPKE RFC]
written in [hacspec].

The recommended entry point is the [hpke rustdoc page].

## Build & Tests
This HPKE specification can be built and tested like regular Rust code.

Use `cargo build` to build it and `cargo test` to test it.

### HACL backend
The hacspec implementation has an efficient crypto backend using HACL*/Evercrypt.
To use it instead of the hacspec crypto backend the `evercrypt` feature can be used,
e.g. `cargo bench --features evercrypt`.

## hacspec
In order to typecheck the hacspec code and extract the F* code again the `test_and_check.sh`
script can be used.

[HPKE RFC]: https://datatracker.ietf.org/doc/draft-irtf-cfrg-hpke/
[hacspec]: https://hacspec.org
[hpke rustdoc page]: https://tech.cryspen.com/hpke-spec
