#!/bin/bash -e
#
# rsync from website checkout to generator source.
# Committing to the website first pushes updates much faster, without needing
# to recompile the whole repo.
#

SRC=../dot-iris.github.io
[ -d "$SRC" ] || {
  echo "Source not found"
  exit 1;
}

rsync -C --exclude coqdoc --exclude .git -avc $SRC/ website/ "$@"
