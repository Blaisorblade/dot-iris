#!/bin/bash -ex
RUN=0

incRun() {
  idx="$1"
  doReboot="$2"

  if [ "$RUN" = "$idx" ]; then
    cd /vagrant
    sed -r --in-place -e "s/^(RUN)=$idx/\1=$[i + 1]/" root-provision.sh
    if [ "$doReboot" = "true" ]; then
      cat <<EOF
Because the kernel was upgraded, you must reboot the machine to use the new kernel *before* installing the new guest additions!
The provisioning script have been modified to proceed next time.

vagrant reload; vagrant provision
EOF
      exit 0
    fi
  fi
}

# # Disable backports
# sed -r -e 's!^(.*-backports.*)$!#\1!' -i /etc/apt/sources.list
# # Switch to auto-selected mirror
# sed -r -e 's!http://.*archive\.ubuntu\.com/ubuntu/?!mirror://mirrors.ubuntu.com/mirrors.txt!' -i /etc/apt/sources.list

apt-get update
apt-get dist-upgrade -y
packages="tmux git build-essential perl make nano vim m4 linux-headers-generic"
#emacs
apt-get install -y $packages
apt-get install -y --no-install-recommends opam
# XXX drop ocaml-nox ? but then opam?
apt-get install -y --no-install-recommends ocaml-nox

# We need to reboot here, to use the new kernel
incRun 0 true
# Remove the old one
apt-get purge -y linux-image-5.4.0-26-generic linux-modules-5.4.0-26-generic linux-modules-extra-5.4.0-26-generic || true

if [ "$RUN" = "1" ]; then
  mkdir -p /media/cdrom && mount /dev/cdrom /media/cdrom -o ro || true
  sh /media/cdrom/VBoxLinuxAdditions.run -- --force || true
  modprobe -r vboxsf || true
  modprobe vboxsf
  mount vagrant /vagrant -t vboxsf -o uid=1000,gid=1000,rw
fi

#apt-get clean
