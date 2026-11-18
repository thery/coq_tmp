#!/bin/sh
# Regenerate every text of the example files with some switches set, into
# examples-NAME/, from a copy of this directory (examples/ and the .vo
# files here are not touched).  Prints, per example file, the time of its
# Explain commands (sum of Rocq's Time).
#   usage: sh make_variant.sh NAME [VAR=VALUE ...]
#   e.g.   sh make_variant.sh staged-none XTEXT_TRANSLATION=staged XTEXT_CONTRACTION=none
#          sh make_variant.sh direct XTEXT_TRANSLATION=direct
# The switches are read when Explain runs (see Explain.v), so the example
# files are compiled again with them.
name=$1; shift
for setting in "$@"; do export "$setting"; done
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi4 2>/dev/null)"
here=$(pwd)
lexicon=$(cd ../lexicon && pwd)
prooftext=$(cd ../prooftext && pwd)
copy=$(mktemp -d)
rsync -a --exclude 'examples*' --exclude cyp-check ./ "$copy/"
mkdir -p "$copy/examples" "$here/examples-$name"
cd "$copy" || exit 1
rocq c -R . XText -Q "$lexicon" Lexicon -Q "$prooftext" ProofText Explain.v || exit 1
for f in paper lemmas inductive thesis stdlib elim_type partial; do
  rocq c -R . XText -Q "$lexicon" Lexicon -Q "$prooftext" ProofText $f.v > log.txt 2>&1 || { echo "FAIL $f"; cat log.txt; }
  printf "%s\t%s\n" $f "$(grep 'Finished transaction' log.txt | awk '{s+=$4} END {print s}')"
done
cp examples/*.md "$here/examples-$name/"
cd "$here" && rm -rf "$copy"
