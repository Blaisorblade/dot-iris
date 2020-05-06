#!/bin/bash -ex
git clone https://github.com/Blaisorblade/dot-iris.git

cd dot-iris

# opam_base_compiler=ocaml-system
# opam switch create ${opam_base_compiler} --locked
eval $(opam env)
opam install -y --deps-only .
time make -j2
make html
