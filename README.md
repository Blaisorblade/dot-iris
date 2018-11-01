# Iris version

Install Iris commit 19e8581017fd4d5118a3cb5afc066a55992ecc57, for instance via
`opam install coq-iris.dev.2018-11-01.2.19e85810`.

# To use glorious opam 2.0

One can use opam 2.0 to create a local switch, that is, a local version of iris
and of coq that will only be used when one is inside this directory. _The first
time,_ one should do:

```shell
opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git --set-default
```

to add the iris opam repository, and then, in this directory, do

```shell
opam switch create . --deps-only --locked
```

to create the local switch. Then, every time you wants to work on this, do

```shell
eval $(opam env)
```

so that `coqc`, etc, correspond to the local version.
