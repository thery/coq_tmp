#!/bin/sh
# Run cyp on its own examples and demos and keep what they print, to check
# that a change to cyp does not change their results.
#   usage: sh gaps_regress.sh OUTDIR
# OUTDIR/NAME.out: cyp's messages (the .md) or Rocq's output (the .v), with
# the times printed by CYP_TIME; OUTDIR/NAME.json: the statuses of the steps.
out=$1; mkdir -p "$out"; out=$(cd "$out" && pwd)
here=$(cd "$(dirname "$0")" && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi4 2>/dev/null)"
export CYP_LIB="$here/vernac" CYP_TIME=1
exe=${CYP_EXE:-$here/_build/default/bin/cyp.exe}
ulimit -v 8000000
for md in "$here"/examples/*.md "$here"/vernac/*.md; do
  case $md in *.checked.md) continue ;; esac
  n=$(basename "$md" .md)
  s=$(date +%s%N)
  nice -n 19 timeout 300 "$exe" "$md" > "$out/$n.out" 2>&1
  echo "total $(( ($(date +%s%N) - s) / 1000000 )) ms" >> "$out/$n.out"
  j=${md%.md}.cyp.json; [ -f "$j" ] && cp "$j" "$out/$n.json"
done
cd "$here/vernac" || exit 1
for v in vc_demo vc_file bare_demo square_pos named_v wrong; do
  s=$(date +%s%N)
  nice -n 19 timeout 300 rocq c -Q . CypV -Q ../../lexicon Lexicon $v.v > "$out/$v.v.out" 2>&1
  echo "exit $? total $(( ($(date +%s%N) - s) / 1000000 )) ms" >> "$out/$v.v.out"
done
