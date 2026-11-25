#!/bin/bash
# Check of cyp's debugging tools (README.md, "Debugging a text"): on each
# example (examples/NAME.md, in a temporary copy of examples/),
#   1. cyp --stats runs and prints a line "cyp: stats" for each condition;
#   2. cyp --only N runs on its first proved condition N;
#   3. every condition it proved is written by cyp --extract N as a Rocq
#      file, which must compile alone: its lemma closed by the script cyp
#      gives for N, its proof term counted by CypTermStats; the count of
#      matches must be the one of the proof cyp built (in the file's
#      comment), the other counts are printed when they differ.  A condition
#      whose context has holes (a formula whose implicit arguments the proof
#      of another step fixes: --extract does not run the other steps) is
#      counted apart: Rocq cannot read its file.
#   usage: bash debug_check.sh [NAME ...]     (exit 1 on a failure)
# Needs: the cyp library compiled in vernac and the driver built (as
# examples_check.sh).
here=$(cd "$(dirname "$0")" && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)"
export CYP_LIB="$here/vernac"
exe=${CYP_EXE:-$here/_build/default/bin/cyp.exe}
[ -x "$exe" ] || { echo "debug_check: no driver $exe (dune build ./bin/cyp.exe)"; exit 2; }
ulimit -v 8000000
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
cp -r "$here/examples" "$tmp/examples"
flags="-Q $CYP_LIB CypV -Q $here/../lexicon Lexicon -Q $here/../prooftext ProofText"
status=0; nx=0; nd=0; nh=0
if [ $# -gt 0 ]; then names="$*"; else
  names=$(cd "$tmp/examples" && ls *.md | grep -v '\.checked\.md$\|^README\.md$' | sed 's/\.md$//'); fi
for name in $names; do
  md=$tmp/examples/$name.md
  "$exe" --stats "$md" > "$tmp/$name.stats" 2>&1
  if ! grep -q '^cyp: stats ' "$tmp/$name.stats"; then
    echo "debug_check: $name: no stats line"; cat "$tmp/$name.stats"; status=1; continue
  fi
  # the conditions proved: "cyp: stats N T ms, ... hyps=K, HOW", HOW not a failure
  ids=$(sed -n 's/^cyp: stats \([0-9.]*\) [0-9]* ms, .* hyps=[0-9]*, \(.*\)$/\1 \2/p' "$tmp/$name.stats" |
        grep -v ' failed after trying' | cut -d' ' -f1)
  first=$(echo "$ids" | head -1)
  if [ -n "$first" ]; then
    "$exe" --only "$first" --stats "$md" > "$tmp/$name.only" 2>&1
    if ! grep -q "^cyp: stats $first " "$tmp/$name.only"; then
      echo "debug_check: $name: --only $first printed no stats line"; cat "$tmp/$name.only"; status=1
    fi
  fi
  for id in $ids; do
    nx=$((nx + 1))
    out=$("$exe" --extract "$id" "$md" 2>&1)
    v=$(echo "$out" | sed -n 's/^cyp: condition .* written to \(.*\)$/\1/p')
    if [ -z "$v" ] || [ ! -f "$v" ]; then
      echo "debug_check: $name $id: nothing extracted"; echo "$out"; status=1; continue
    fi
    res=$( (cd "$(dirname "$v")" && rocq c $flags "$(basename "$v")") 2>&1 | grep -v '^\[\|^Warning\|^File .*line\|^ *$')
    got=$(echo "$res" | sed -n 's/^cyp: term [^ ]* \(.*\)$/\1/p')
    want=$(sed -n "s/^   the proof cyp built: \(.*\)$/\1/p" "$v")
    if [ -z "$got" ] && grep -q "^   holes: " "$v"; then
      nh=$((nh + 1)); echo "debug_check: $name $id: holes in the context (another step fixes them), the file does not compile"
    elif [ -z "$got" ]; then
      echo "debug_check: $name $id: the extracted file does not compile"; echo "$res" | head -20; status=1
    elif [ "$(echo "$got" | sed 's/.*matches=\([0-9]*\).*/\1/')" != "$(echo "$want" | sed 's/.*matches=\([0-9]*\).*/\1/')" ]; then
      echo "debug_check: $name $id: matches differ: cyp $want, extracted $got"; status=1
    elif [ "$got" != "$want" ]; then
      nd=$((nd + 1)); echo "debug_check: $name $id: cyp $want | extracted $got"
    fi
  done
done
echo "debug_check: $nx conditions extracted, $((nx - nh)) compiled ($nh with holes in their context), $nd with other counts that differ (status $status)"
exit $status
