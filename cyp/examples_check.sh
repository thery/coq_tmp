#!/bin/bash
# Regression test of cyp's JSON output: cyp is run on each example
# (examples/NAME.md) in a temporary copy of examples/, and the JSON it
# writes (NAME.cyp.json: the steps, their lines, statuses, formulas and
# roles, and the justification words with the place of their declaration)
# is compared with the committed examples/NAME.cyp.json.
#   usage: bash examples_check.sh            (exit 1 on a difference)
#          bash examples_check.sh --update   (rewrite the committed files)
# The paths of the copy are written cyp/examples/ (a JSON names the file
# of a declaration), so that the committed files do not depend on the
# machine.  A change to cyp that moves the declarations in vernac/Cyp.v
# changes their "line" fields: check the difference, then --update.
# Needs: the cyp library compiled in vernac (rocq c -Q . CypV -Q
# ../../lexicon Lexicon -Q ../../prooftext ProofText Cyp.v) and the
# driver built (dune build ./bin/cyp.exe).
here=$(cd "$(dirname "$0")" && pwd)
update=no; [ "${1:-}" = --update ] && update=yes
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)"
export CYP_LIB="$here/vernac"
exe=${CYP_EXE:-$here/_build/default/bin/cyp.exe}
[ -x "$exe" ] || { echo "examples_check: no driver $exe (dune build ./bin/cyp.exe)"; exit 2; }
ulimit -v 8000000
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
cp -r "$here/examples" "$tmp/examples"
status=0; n=0; changed=""
for md in "$tmp"/examples/*.md; do
  case $md in *.checked.md|*/README.md) continue ;; esac
  name=$(basename "$md" .md)
  rm -f "${md%.md}.cyp.json"
  nice -n 19 "$exe" "$md" > "$tmp/$name.out" 2>&1
  j=${md%.md}.cyp.json
  if [ ! -f "$j" ]; then
    echo "examples_check: cyp wrote no $name.cyp.json (see its messages:)"; cat "$tmp/$name.out"; status=1; continue
  fi
  n=$((n + 1))
  sed "s|$tmp/examples/|cyp/examples/|g" "$j" > "$tmp/$name.norm.json"
  ref=$here/examples/$name.cyp.json
  if ! cmp -s "$tmp/$name.norm.json" "$ref"; then
    if [ $update = yes ]; then
      cp "$tmp/$name.norm.json" "$ref"; changed="$changed $name"
    else
      echo "examples_check: $name.cyp.json differs:"
      diff <(tr ',' '\n' < "$ref" 2>/dev/null) <(tr ',' '\n' < "$tmp/$name.norm.json") | head -20
      status=1
    fi
  fi
done
if [ $update = yes ]; then
  echo "examples_check: $n examples, rewritten:${changed:- none}"
else
  [ $status = 0 ] && echo "examples_check: the JSON of the $n examples are the committed ones"
fi
exit $status
