#!/bin/bash
#
## Produce documentation from the `.v` files passed on the command line.
#
target=sel-html

make -j4 -f Makefile.coq $(ls "$@"|while read i; do echo "${i}o"; done)

rm -rf $target
mkdir -p $target
"coqdoc" \
	-toc --toc --toc-depth 2 --html --interpolate --index indexpage --no-lib-name --parse-comments --utf8 -html  -Q theories D  -d $target "$@"
