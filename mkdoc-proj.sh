#!/bin/bash
#
## Produce documentation from the first N files from _CoqProject, where N is
## passed on the command line.
#
nlines="$1"
./mkdoc.sh $(cat _CoqProject|egrep -v '^($|-|#)'|head -${nlines})
