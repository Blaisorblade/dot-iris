#!/bin/bash -ex

# # Disable backports
# sed -r -e 's!^(.*-backports.*)$!#\1!' -i /etc/apt/sources.list
# # Switch to auto-selected mirror
# sed -r -e 's!http://.*archive\.ubuntu\.com/ubuntu/?!mirror://mirrors.ubuntu.com/mirrors.txt!' -i /etc/apt/sources.list

apt-get update
apt-get upgrade -y
packages="tmux git build-essential perl make nano vim m4 linux-headers-generic"
#emacs
apt-get install -y $packages
apt-get install -y --no-install-recommends opam
# XXX drop ocaml-nox ? but then opam?
apt-get install -y --no-install-recommends ocaml-nox

#apt-get clean
