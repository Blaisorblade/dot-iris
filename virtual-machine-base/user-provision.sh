#!/bin/bash -ex

opam_base_compiler=ocaml-system
#opam_base_compiler=ocaml-variants.4.07.1+flambda

opam init --dot-profile=~/.bashrc -c ${opam_base_compiler} -a
eval $(opam env)

echo 'set bg=dark' >> ~/.vimrc

opam repo add coq-released https://coq.inria.fr/opam/released --set-default --all
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git --set-default --all
opam repo add bb-overlay https://github.com/Blaisorblade/opam-overlay.git --set-default --all
opam update -y
opam pin -y --no-action add -k version coq 8.11.1+flambda-native
opam pin -y --no-action add -k version coq-autosubst dev.coq86
opam install -y coq coq-autosubst
