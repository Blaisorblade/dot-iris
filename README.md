# Type Soundness for DOT via logical relations

Mechanization accompanying the paper "Scala Step-by-step: Soundness for
DOT with Step-Indexed Logical Relations and Iris".

The mapping between the paper and this mechanization is described in
`./correspondence.md`.

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
  - `synLemmas.v`: (SYNtactic Lemmas): lemmas about syntax and binding.
  - `rules.v`: lemmas about this language's operational semantics.
* `lr`: logical relation, semantic typing, compatibility lemmas
  - `path_wp.v`: define path weakest precondition;
  - `dlang_inst.v`: instantiate shared Iris setup from `dlang.v`;
  - `unary_lr.v`: definition of unary logical relation.
  Compatibility lemmas:
  - `lr_lemmasDefs.v`: lemmas about DEFinition typing;
  - `lr_lemmasTSel.v`: lemmas about TSel (type selection);
  - `lr_lemmasNoBinding.v`: various typing lemmas, not requiring `synLemmas.v`;
  - `lr_lemmas.v`: other misc typing lemmas.
* `stamping`: definitions and lemmas about stamping.
* `typing`: syntactic typing and auxiliary lemmas about it
  - `typingStamping.v`: prove stamping of typing derivations.
* `examples`: various gDOT snippets.
* `fundamental.v`: prove fundamental theorem, adequacy and type safety.

## Installation
### Iris version

Install the Coq and Iris version specified in `opam`, for instance via
`opam install coq-iris.<insert version here>`.

### To use opam 2.0

One can use opam 2.0 to create a local switch, that is, a local version of iris
and of coq that will only be used when one is inside this directory. _The first
time,_ one should do:

```shell
opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git --set-default --all
```

to add the iris opam repository, and then, in this directory, do

```shell
opam switch create . --locked
```

to create the local switch. Then, every time you wants to work on this, do

```shell
eval $(opam env)
```

so that `coqc`, etc, correspond to the local version. You can also configure
opam to do this automatically by answering yes when `opam init` asks you the
following:
"A hook can be added to opam's init scripts to ensure that the shell remains in sync with the opam environment when they are loaded. Set that up?"

To answer that question again, check `opam init` docs; `opam init --reinit`
works here.

### Upgrading switch

Use

```
opam install .
```

to upgrade the switch when we bump dependencies (which for now we do seldom).
To make this succeed, you might need to first run `opam unpin coq-stdpp
coq-iris`, `opam uninstall dot-iris`, `opam uninstall .`, or such.

After updating deps, you will need to do a clean build, so `make clean` and then
`make`.

## Development/Additional docs (not relevant to paper)

See `development.md`.
