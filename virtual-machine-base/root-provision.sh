#!/bin/bash -ex

# Disable backports
sed -r -e 's!^(.*-backports.*)$!#\1!' -i /etc/apt/sources.list
# Switch to auto-selected mirror
sed -r -e 's!http://.*archive\.ubuntu\.com/ubuntu/?!mirror://mirrors.ubuntu.com/mirrors.txt!' -i /etc/apt/sources.list

apt-get update
apt-get upgrade -y
#linux-headers-generic perl
packages="build-essential
  make m4
  tmux git
  nano vim emacs-nox
  aptitude"
apt-get install -y $packages
apt-get install -y --no-install-recommends opam
# Maybe drop ocaml-nox and replace it by optimized version? Hm not worth it.
apt-get install -y --no-install-recommends ocaml-nox

apt-get clean
