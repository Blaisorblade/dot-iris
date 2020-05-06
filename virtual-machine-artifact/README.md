# Base Vagrant image for dot-iris

This directory contains code to prepare a virtual machine using Vagrant,
containing dot-iris and all its dependencies.

## Usage

- First, follow instructions in
[`../virtual-machine-base`](../virtual-machine-base).
- Then, create a VM using Vagrant, and shut it down:

  ```shell
  vagrant up
  vagrant halt
  ```

  This will produce a VirtualBox VM named `dotIrisVm`.
- Finally, use the VirtualBox GUI to export the `dotIrisVm` VM via "> File >
  Export Appliance...".

Tested with VirtualBox 6.1.6 and Vagrant 2.2.7.
