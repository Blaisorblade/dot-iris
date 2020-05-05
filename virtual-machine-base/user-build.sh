#!/bin/bash -ex
git clone https://github.com/Blaisorblade/dot-iris.git

cd dot-iris

# opam_base_compiler=ocaml-system
# opam switch create ${opam_base_compiler} --locked
opam install -y --deps-only .
make -j2 TIMED=1
make html
