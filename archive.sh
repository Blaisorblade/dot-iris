#!/bin/sh
archivePrefix=gdot-iris-coq
archiveName=$archivePrefix.zip
rm -f $archiveName
git archive -o $archiveName --prefix $archivePrefix/ HEAD
