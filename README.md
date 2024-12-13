# kanon-aeneas

We verify correctness of a simple k-anonymity implementation in Rust using
[Aeneas](https://github.com/AeneasVerif/aeneas). Aeneas is a compiler that translates Rust code to a
variety of proof assistant backends like Lean, Coq, and others. We use Lean as a backend of choice
and encode the specification for the implementation.

Aeneas relies on a translation from Rusts's MIR internal language to a pure lambda calculus. It is
intended to be used in combination with [Charon](https://github.com/AeneasVerif/charon), which
compiles Rust programs to an intermediate representation called LLBC.

The Rust implementation of the algorithm is located in `kanon/src/kanon.rs`. To translate it to
Lean, first clone Aeneas via `git submodule update --init`. Then, follow the instructions from
Aeneas to build it. Once you are done, run `make build` from the `kanon` directory to retrieve the
result of the translation.

For your reference, the result of the transformation is also provided in
`kanon_lean/KanonLean/Funs.lean`. `kanon_lean/KanonLean/Properties.lean` contains the specification
and proofs, which can be checked via running `lake build` from the `kanon_lean` directory. Note that
Aeneas provides a library with primitives for developing proofs, so make sure to run `git submodule
update --init` before attempting to build the project.

Specification for each function in `Properties.lean` is tagged with `@[pspec]`, so that using
`progress` tactic in any proof containing the function could make use of it. Due to the limitations
of Aeneas, the Rust implementation is iterator-free and makes use of `while` loops instead (`for`
loops in Rust are iterator-based). Due to this, we had to write a separate specification and proof
for each loop of the program, which roughly corresponded to identifying the loop invariants and
variants.

Lastly, we made an attempt to consolidate the proofs using tactics like `repeat`, which led to
slightly more concise code.
