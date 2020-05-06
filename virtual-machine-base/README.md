# Base Vagrant image for Coq

This directory contains code to prepare a _base_ virtual machine using Vagrant,
containing a suitable Coq installation.

In turn, this VM can be used to prepare the _actual_ virtual machine to use,
containing the right version of dependencies, together with dot-iris.

## Usage

Install VirtualBox and Vagrant, then run:

```shell
./box-package.sh --clean
```

this will add a base box `dot-iris-base`:

```shell
$ vagrant box list
bento/ubuntu-20.04 (virtualbox, 202004.27.0)
dot-iris-base      (virtualbox, 0)
```

Tested with VirtualBox 6.1.6 and Vagrant 2.2.7.
