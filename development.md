# Development Instructions

## Creating a local opam switch

Instead of installing dependencies globally, one _can_ use opam 2.0 to create a
separate switch. That _can_ be a local switch, i.e., a local version of Iris
and of Coq that will only be used when the shell is inside `dot-iris` directory.
Global switches can be useful, but for those we refer to `opam`'s docs. We
provide instructions for local switches in this file.

_The first time,_ after installing and configuring `opam`, one should run:

```shell
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released --set-default --all
opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git --set-default --all
opam update
```

to add the Iris opam repository, and then, in the `dot-iris` directory, do:

```shell
opam switch create . -y ocaml-variants.4.07.1+flambda --locked
eval $(opam env)
```

to create the local switch.
This will also install all needed packages, from the OCaml
compiler to Coq and all dependencies, and take a while (10-30 minutes).

Then, every time you wants to work on this project,
`cd` to `dot-iris`'s folder and run:

```shell
eval $(opam env)
```

so that `coqc`, etc., correspond to the local version.

If you want to automate the `eval $(opam env)` step, you can rerun `opam init`'s
configuration wizard via `opam init --reinit`, and answer "yes" when opam asks:

> A hook can be added to opam's init scripts to ensure that the shell remains in
> sync with the opam environment when they are loaded. Set that up?

## Upgrading switch

Use, in `dot-iris`'s folder:

```
opam install .
```

to upgrade the switch when we bump dependencies (which for now we do seldom).
To make this succeed, you might need to first run `opam unpin coq-stdpp
coq-iris`, `opam uninstall dot-iris`, `opam uninstall .`, or such.

After updating the dependencies, you will need to do a clean build, so run
`make clean` before `make`.

## Removing switch

Use, in `dot-iris`'s folder:

```
opam switch remove .
```

## Bumping Iris

Find the version name on top of
https://gitlab.mpi-sws.org/iris/opam/commits/master/packages/coq-iris, then
modify `opam`, *commit*, and reinstall with `opam install .`

## Additional developments, not used in the paper

* [`theories/DSub`](theories/DSub): guarded D<:, incomplete, used for prototyping.
* [`theories/DSubSyn`](theories/DSubSyn): guarded D<:, complete.
  This code demonstrates a simpler modeling technique: type members are
  represented by storing syntactic types in values, and interpreting them
  recursively. Used for prototyping but mostly complete. Shares code from
  `theories/DSub`.

Inside the `Dot` folder:
* [`misc_unused`](theories/Dot/misc_unused): misc stuff, not used elsewhere or
  relevant to the paper.
