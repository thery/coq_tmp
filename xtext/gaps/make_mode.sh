#!/bin/sh
# Write all the English texts of xtext with one setting of its switches,
# from a copy of xtext/ (examples/ and the .vo files here are not touched).
#   usage: sh make_mode.sh CONTRACTION ANNOTATION OUTDIR
# e.g. sh make_mode.sh maximal thesis /tmp/max-thesis
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi4 2>/dev/null)"
xt=$(cd "$(dirname "$0")/.." && pwd)
lex=$(cd "$xt/../lexicon" && pwd)
out=$3
mkdir -p "$out"
d=$(mktemp -d)
rsync -a --exclude examples --exclude examples-thesis --exclude cyp-check --exclude gaps "$xt/" "$d/"
mkdir -p "$d/examples"
cd "$d" || exit 1
export XTEXT_CONTRACTION=$1 XTEXT_ANNOTATION=$2
rocq c -R . XText -Q "$lex" Lexicon Explain.v || exit 1
for f in paper lemmas inductive thesis stdlib elim_type; do
  rocq c -R . XText -Q "$lex" Lexicon $f.v > log.txt 2>&1 || { echo "FAIL $f"; cat log.txt; }
done
cp examples/*.md "$out/"
rm -rf "$d"
