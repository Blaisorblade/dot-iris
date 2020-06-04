#!/bin/bash
EXTRA_DIR=coqdocjs/extra
COQDOCFLAGS="\
  --external https://plv.mpi-sws.org/coqdoc/stdpp/ stdpp \
  --external https://plv.mpi-sws.org/coqdoc/iris/ iris \
  --external https://www.ps.uni-saarland.de/autosubst/doc/ Autosubst \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments --utf8 \
  --with-header ${EXTRA_DIR}/header.html --with-footer ${EXTRA_DIR}/footer.html"

coqdoc $COQDOCFLAGS "$@"
