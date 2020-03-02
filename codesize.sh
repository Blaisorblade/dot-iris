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
sumDirsRaw() {
  res=$(for i in $1; do
    checkEmpty $i
    totsize $i
  done | sum)
  echo $res
}
format() {
  echo "$1 ($2): $3"
}

sumDirs() {
  format "$1" "$2" "$(sumDirsRaw "$2")"
}

# total() {
#   sumDirs "$1" "$(find . -type d)"
# }

cat << EOF
# Code size statistics

Computed by running \`./codesize.sh > codesize.md\` on commit
$(git rev-parse HEAD).

Saved output:
\`\`\`
EOF

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

prelimDirs=". iris_extra pure_program_logic"
prelimLoc=$(sumDirsRaw "$prelimDirs")
dotDirs="$(echo $(find Dot -type d \( -name misc_unused -prune -o -print \)))"
dotLoc=$(sumDirsRaw "$dotDirs")

echo
format "Preliminaries + DOT" "$prelimDirs $dotDirs" "$[$prelimLoc + $dotLoc]"

echo
format "Preliminaries" ". iris_extra pure_program_logic" $prelimLoc

echo
format "DOT" "$dotDirs" "$dotLoc"

echo
cd Dot
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

echo '```'
