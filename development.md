# Development Instructions

## Installation for contributors

### Coq/Iris version

The supported Coq and Iris versions are specified in `opam`; we currently assume
Coq 8.11.1 (and we know of bugs in both 8.10.2 and 8.11.0).

Install those exact versions, for instance via
`opam install coq.8.11.1 coq-iris.<insert version here>`.

### To use opam 2.0 switches

One can use opam 2.0 to create a local switch, that is, a local version of iris
and of coq that will only be used when one is inside this directory. _The first
time,_ one should do:

```shell
opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git --set-default --all
```

to add the iris opam repository, and then, in this directory, do

```shell
opam switch create . ocaml-base-compiler.4.09.0 --locked
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


### Additional developments, not used in the paper
Inside the `Dot` folder:
* `misc_unused`: misc stuff, not used elsewhere or relevant to the paper.

* `theories/DSub`: guarded D<:, incomplete, used for prototyping.
* `theories/DSubSyn`: guarded D<:, where type members are represented by
  storing syntactic types in values, and interpreting them recursively. Used for
  prototyping but mostly complete. Shares code from `theories/DSub`.

### Bumping Iris

Find the version name on top of
https://gitlab.mpi-sws.org/iris/opam/commits/master/packages/coq-iris, then
modify `opam`, *commit*, and reinstall with `opam install .`
