# ICFP 2020 Artifact

Name:    **Scala Step-by-Step: Soundness for DOT with Step-Indexed Logical Relations in Iris**

Authors: **Paolo G. Giarrusso, Léo Stefanesco, Amin Timany, Lars Birkedal and Robbert Krebbers**

## Artifact Instructions

Our artifact is a mechanized proof using the Coq proof assistant.

We provide both a source tarball, and a virtual machine where we have installed
these sources and their dependencies.

### Source Tarball

Our source tarball contains:
- the source code;
- generated coqdoc in `golden-html` - start browsing from
  [`golden-html/coqdoc/index.html`](golden-html/coqdoc/index.html);

Proceed browsing with [`README.md`](README.md).

The compilation time is around 5 minutes on my laptop (with `make -j4`), but
installing dependencies takes more than that (10-30 minutes).

### Virtual machine

SSH into the virtual machine per instructions below. The sources are in
`~/dot-iris`, as a checkout of the branch `final-artifact`.

We have already compiled the sources with `make html`, and saved the generated
coqdoc as `golden-html`.

Compilation inside the VM of `dot-iris` itself (on one CPU) took ~15minutes.

To compile `dot-iris` again from scratch, run `make clean` before running
`make`.

## QEmu Instructions

The ICFP 2020 Artifact Evaluation Process is using a Debian QEmu image as a
base for artifacts. The Artifact Evaluation Committee (AEC) will verify that
this image works on their own machines before distributing it to authors.
Authors are encouraged to extend the provided image instead of creating their
own. If it is not practical for authors to use the provided image then please
contact the AEC co-chairs before submission.

QEmu is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEmu can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEmu homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See https://wiki.archlinux.org/index.php/QEMU for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10
Download and install QEmu via the links on https://www.qemu.org/download/#windows.
Ensure that qemu-system-x86_64.exe is in your path.
Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".
Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.



### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with 'sudo' to start the VM. If the VM does not
start then check `Debugging.md`

Once the VM has started you can login to the guest system from the host using:

```
$ ssh -p 5555 artifact@localhost             (password is 'password')
```

You can also copy files to and from the host using scp, eg:

```
$ scp -P 5555 artifact@localhost:somefile .  (password is 'password')
```

The root account password is ``password``.

The default user is username:```artifact``` password:```password```.


### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use:

```
$ sudo shutdown now
```


### Artifact Preparation

Authors should install software dependencies into the VM image as needed,
preferably via the standard Debian package manager. For example, to install
GHC and cabal-install, login to the host and type:

```
$ sudo apt update
$ sudo apt install ghc
$ sudo apt install cabal-install
```

If you really need a GUI then you can install X as follows, but we prefer
console-only artifacts whenever possible.

```
$ sudo apt-get install xorg
$ sudo apt-get install xfce4   # or some other window manager
$ startx
```

See Debugging.md for advice on resolving other potential problems,
particularly when installing the current version of Coq via opam.

If your artifact needs lots of memory you may need to increase the value
of the ```QEMU_MEM_MB``` variable in the ```start.sh``` script.

When preparing your artifact, please also follow the guidelines at:
 https://icfp20.sigplan.org/track/icfp-2020-artifact-evaluation#Forms-of-Artifacts
