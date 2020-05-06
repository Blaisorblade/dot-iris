#!/bin/bash -ex
if [ "$1" = "--clean" ]; then
  vagrant destroy
  vagrant up
  vagrant halt
fi
vagrant package --base dotIrisVmBase --output dot-iris-base.box
vagrant box add --name dot-iris-base dot-iris-base.box
