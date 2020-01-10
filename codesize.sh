#!/bin/bash
checkEmpty() {
  ls $1/*.v &> /dev/null
}

totsize() {
  wc -l $1/*.v | tail -1|awk '{print $1}'
}
sum() {
  awk '{s+=$1} END {print s}'
}
sumDirs() {
  echo -n "$1 ($(echo $2)): "
  for i in $2; do
    checkEmpty $i
    totsize $i
  done | sum
}
# total() {
#   sumDirs "$1" "$(find . -type d)"
# }

cd theories
find . -type d |
  while read i; do
    checkEmpty $i || continue
    tot=$(totsize $i)
    echo "theories${i#.}: $tot"
    #wc -l $i/*.v | tail -1|awk '{printf "total: %d; ", $1}'
    # coqwc $i/*.v | tail -1|
    #   awk '{printf "spec: %d, proof: %d, comments: %d\n", $1, $2, $3}'
  done

echo
sumDirs "Unused" "misc_unused Dot/misc_unused DSub/misc_unused"
echo
sumDirs "Preliminaries" ". iris_extra pure_program_logic"
cd Dot
echo
sumDirs "DOT" "$(find . -type d \( -name misc_unused -prune -o -print \))"

echo
sumDirs "syntax" "syn"
sumDirs "logrel" "lr"
sumDirs "model (syntax + logrel)" "syn lr"

echo
sumDirs "syntactic typing (w/ stamping)" ". typing stamping"

echo
sumDirs "examples" "examples"

# cd DSub
# echo "DSub"
# sumDirs "DSub syntax" "syn"
# cd ..

# cd DSubSyn
# sumDirs "DSub syntax" "syn"
# cd ..
