#!/bin/sh
# Regenerate every text with the strategy xtext-annotation "double"
# (types.elpi) into examples-double/, from a copy of this directory (so
# that examples/ and the .vo files here are not touched).  Prints, per
# example file, the time of the Explain commands (sum of Rocq's Time).
# usage: sh make_double.sh
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi4 2>/dev/null)"
here=$(pwd)
lex=$(cd ../lexicon && pwd)
d=$(mktemp -d)
rsync -a --exclude examples --exclude examples-double --exclude cyp-check ./ "$d/"
mkdir -p "$d/examples" "$here/examples-double"
cd "$d" || exit 1
export XTEXT_ANNOTATION=double
rocq c -R . XText -Q "$lex" Lexicon Explain.v || exit 1
for f in paper lemmas inductive thesis stdlib elim_type partial; do
  rocq c -R . XText -Q "$lex" Lexicon $f.v > log.txt 2>&1 || { echo "FAIL $f"; cat log.txt; }
  printf "%s\t%s\n" $f "$(grep 'Finished transaction' log.txt | awk '{s+=$4} END {print s}')"
done
cp examples/*.md "$here/examples-double/"
echo "$d"
