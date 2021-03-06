# Type Soundness for DOT via logical relations

[![Build Status](https://travis-ci.org/Blaisorblade/dot-iris.svg?branch=master)](https://travis-ci.org/Blaisorblade/dot-iris)
[![Artifact DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.3926703.svg)](https://doi.org/10.5281/zenodo.3926703)

Mechanization accompanying the paper [Scala Step-by-Step: Soundness for
DOT with Step-Indexed Logical Relations in Iris](https://dot-iris.github.io/),
published at [ICFP 2020](https://dl.acm.org/doi/10.1145/3408996).

The mapping between the paper and this mechanization, together with the
layout of the codebase, is described in [`correspondence.md`](correspondence.md).
See below for how to process sources with coqdoc.

We have also provided [an artifact](https://doi.org/10.5281/zenodo.3926703),
matching our [v1.0](https://github.com/Blaisorblade/dot-iris/tree/v1.0) release.
Its instructions are in [`00Artifact-README.md`](00Artifact-README.md).

## Compiling the Proof the first time

### Requirements

- GNU make
- [opam 2.0.6](https://opam.ocaml.org/doc/Install.html) or later.

### Cloning this repository

After the cloning, run
```
git submodule update --init --recursive
```
to fetch all git submodules.

### Installing dependencies

The following commands will install the correct Coq version and the
correct versions of the std++ and Iris libraries.

- If `opam` is not configured, run its setup wizard with `opam init`.
- Then, prepare for installation with:
```shell
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released --set-default --all
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git --set-default --all
opam update
```
- If you use `opam` for other Coq projects, we recommend setting up a dedicated
  `opam` switch. Instructions appear in [`development.md`](./development.md).
- Actually install dependencies with:
```shell
opam install --deps-only .
```

### Compiling the actual proof

Run `make -jN` to build the full development, where N is the number of your
CPU cores; that should take around 5-10 minutes.

### Browsing published coqdoc

Start from [here](https://dot-iris.github.io/coqdoc/).

### Running coqdoc

Run `make html` to run coqdoc over the code, to obtain an hyperlinked version
(for ease of cross-referencing).
`html/toc.html` offers an index for navigation; keep in mind that
[`correspondence.md`](correspondence.md) is a better overview.

## Documentation for developers / additional docs (not relevant to paper)

See [`development.md`](development.md).
