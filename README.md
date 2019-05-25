# Type Soundness for DOT via logical relations

## File Layout

Code is not perfectly modularized, but here is a rough layout of the various files.

* `theories/`: General infrastructure.
  - tactics.v: misc homegrown Ltac automation
* `theories/DSub`: (guarded) D<:
* `theories/DSubSyn`: (guarded) D<:, where type members are represented by
  storing syntactic types in values, and interpreting them recursively.

In each folder:
* Syntax:
  - `*syn*`.v: SYNtax, based on dotsyn_orig.v
  - synLemmas.v: (SYNtactic Lemmas): lemmas about syntax and binding.
* Operational semantics
  - operational.v: instantiate Iris with DOT operational semantics
  - rules.v: lemmas about WP and this language's semantics.

* Unary logical relation:
  - `unary_lr.v`: definition of logical relation
  - `unary_lr_binding.v`: binding-related lemmas on the logical relation
* (Sub)typing lemmas about unary logical relation:
  - lr_lemmasDefs.v: lemmas about DEFinition typing
  - lr_lemmasTSel.v: lemmas about TSel (type selection)
  - lr_lemma_nobinding.v: various typing lemmas, not requiring `unary_lr_binding.v`.
  - lr_lemma.v: other misc typing lemmas
  - fundamental.v: prove fundamental theorem
  - adequacy.v: relating semantic typing and runtime safety, using Iris WP
    adequacy, and showing the choice of `Σ : gFunctors` is consistent.
* Support
  - experiments.v: various (typing) lemmas that might or might not be useful

## Installation
### Iris version

Install the Iris version specified in opam, for instance via
`opam install coq-iris.<insert version here>`.

### To use glorious opam 2.0

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

### Bumping Iris

Find the version name on top of
https://gitlab.mpi-sws.org/iris/opam/commits/master/packages/coq-iris, then
modify `opam`, *commit*, and reinstall with `opam install .`
