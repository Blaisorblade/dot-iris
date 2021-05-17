#!/bin/bash
checkEmpty() {
  ls $1/*.v &> /dev/null
}

totsize() {
  if ls $1/*.v &> /dev/null; then
    wc -l $1/*.v | tail -1|awk '{print $1}'
  else
    echo 0
  fi
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
$(git rev-parse HEAD~).

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
dotExamplesDirs="$(echo $(find Dot/examples -type d))"
dotExamplesLoc=$(sumDirsRaw "$dotExamplesDirs")
dotDirs="$(echo $(find Dot -type d \( \( -name misc_unused -o -name examples -o -name hkdot \) -prune -o -print \)))"
dotLoc=$(sumDirsRaw "$dotDirs")

echo
format "Preliminaries + DOT" "$prelimDirs $dotDirs" "$[$prelimLoc + $dotLoc]"
format "Examples" "$dotExamplesDirs" "$dotExamplesLoc"
format "Preliminaries + DOT + examples" "$prelimDirs $dotDirs $dotExamplesDirs" "$[$prelimLoc + $dotLoc + $dotExamplesLoc]"

echo
format "Preliminaries" ". iris_extra pure_program_logic" $prelimLoc

echo
format "DOT" "$dotDirs" "$dotLoc"

echo
cd Dot
sumDirs "syntax" "syn"
sumDirs "logrel" "lr semtyp_lemmas"
sumDirs "model (syntax + logrel)" "syn lr semtyp_lemmas"

echo
sumDirs "syntactic typing (w/ fundamental)" ". typing syntyp_lemmas"

echo
sumDirs "hkdot" "hkdot"

echo
cd ..
sumDirs "examples" "$dotExamplesDirs"
# cd DSub
# echo "DSub"
# sumDirs "DSub syntax" "syn"
# cd ..

echo '```'
