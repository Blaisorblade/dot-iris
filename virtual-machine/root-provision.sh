#!/bin/bash -ex
# # Disable backports
# sed -r -e 's!^(.*-backports.*)$!#\1!' -i /etc/apt/sources.list
# # Switch to auto-selected mirror
# sed -r -e 's!http://.*archive\.ubuntu\.com/ubuntu/?!mirror://mirrors.ubuntu.com/mirrors.txt!' -i /etc/apt/sources.list

add-apt-repository ppa:avsm/ppa
apt-get update
# XXX drop ocaml
packages="opam tmux git build-essential perl make nano vim m4 ocaml-nox"
#emacs
apt-get install -y $packages
#apt-get clean

mkdir -p /media/cdrom && mount /dev/cdrom /media/cdrom -o ro || true
sh /media/cdrom/VBoxLinuxAdditions.run -- --force || true
modprobe -r vboxsf || true
modprobe vboxsf
# mount /vagrant /vagrant -t vboxsf -o uid=1000,gid=1000,rw
