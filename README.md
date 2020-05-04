# Type Soundness for DOT via logical relations

[![Build Status](https://travis-ci.org/Blaisorblade/dot-iris.svg?branch=master)](https://travis-ci.org/Blaisorblade/dot-iris)

Mechanization accompanying the paper "Scala Step-by-Step: Soundness for
DOT with Step-Indexed Logical Relations in Iris".

The mapping between the paper and this mechanization, together with the
layout of the codebase, is described in
[correspondence.md](correspondence.md).

## Compiling the Proof the first time
### Requirements
- GNU make
- [opam 2.0.6](https://opam.ocaml.org/doc/Install.html) or later.

### Installing dependencies

The following commands will install the correct Coq version (8.11.1) and the
correct versions of the std++ and Iris libraries.

- If `opam` is not configured, run its setup wizard with `opam init`.
- Then, prepare for installation with:
```shell
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released --set-default --all
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git --set-default --all
opam update
```
- If you use `opam` for other Coq projects, you might want to set up a dedicated
  `opam` switch. Instructions appear in [`development.md`](./development.md).
- Actually install dependencies with:
```shell
opam install --deps-only .
```

### Compiling the actual proof

Run `make -jN` to build the full development, where N is the number of your
CPU cores; that should take around 5-10 minutes.

## Documentation for developers / additional docs (not relevant to paper)

See [`development.md`](development.md).
