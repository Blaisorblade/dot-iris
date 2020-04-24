# Type Soundness for DOT via logical relations

[![Build Status](https://travis-ci.org/Blaisorblade/dot-iris.svg?branch=master)](https://travis-ci.org/Blaisorblade/dot-iris)

Mechanization accompanying the paper "Scala Step-by-Step: Soundness for
DOT with Step-Indexed Logical Relations in Iris".

The mapping between the paper and this mechanization is described in
[correspondence.md](correspondence.md).

## Compiling the Proof the first time
### Requirements
- GNU make
- [opam 2.0.6](https://opam.ocaml.org/doc/Install.html) or later.

### Installing dependencies

The following commands will install Coq 8.11.1 and the correct versions of the std++ and Iris libraries.
```shell
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released --set-default --all
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git --set-default --all
opam install --deps-only .
```

### Compiling the actual proof

Run `make -jN` to build the full development, where N is the number of your
CPU cores; that should take around 5-10 minutes.

## File Layout

Here is a rough layout of the various files.

* `theories/Dot`: guarded DOT. Complete.
* `theories/DSub`, `theories/DSubSyn`: guarded D<:, complete (mentioned in a
  side note in the paper).
* `theories/`: General infrastructure.
* `theories/pure_program_logic`: define a "pure" variant of Iris's weakest
  precondition.
* `theories/iris_extra`: Additional Iris infrastructure.
  - `dlang.v`: instantiate Iris with a language setup for our proofs

Inside the `Dot` folder:
* `syn`: syntax
  - `syn.v`: definition of the basic SYNtax, and instantiate Iris with DOT
    operational semantics.
  - `syn_lemmas.v`: (SYNtactic Lemmas): lemmas about syntax and binding.
  - `rules.v`: lemmas about this language's operational semantics.
* `lr`: logical relation, semantic typing, compatibility lemmas
  - `path_wp.v`: define path weakest precondition;
  - `dlang_inst.v`: instantiate shared Iris setup from `dlang.v`;
  - `unary_lr.v`: definition of unary logical relation.
  Compatibility lemmas:
  - `defs_lr.v`: lemmas about DEFinition typing;
  - `tsel_lr.v`: lemmas about TSel (type selection);
  - `no_binding_lr.v`: various typing lemmas, not requiring `syn_lemmas.v`;
  - `binding_lr.v`: other misc typing lemmas.
* `stamping`: definitions and lemmas about stamping.
* `typing`: syntactic typing and auxiliary lemmas about it
  - `typing_stamping.v`: prove stamping of typing derivations.
* `examples`: various gDOT snippets.
* `fundamental.v`: prove fundamental theorem, adequacy and type safety.

## Documentation for developers / additional docs (not relevant to paper)

See `development.md`.
