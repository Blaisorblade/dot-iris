#!/bin/bash
#
## Produce documentation from the `.v` files passed on the command line.
#
target=sel-html
EXTRA_DIR=coqdocjs/extra

make -j4 -f Makefile.coq $(ls "$@"|while read i; do echo "${i}o"; done)

rm -rf $target
mkdir -p $target
./coqdoc.sh -toc -html \
	-Q theories D  -d $target "$@"
cp ${EXTRA_DIR}/resources/* $target
cd $target; ln -s toc.html index.html
