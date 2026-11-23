#!/bin/sh
# Run cyp (the driver cyp/bin/cyp.ml, Cyp File, switch elpi5) on the given
# examples, copied to cyp-check/, one text at a time; print: name,
# seconds, the nodes proved, not proved, and the remarks (▫️), or "failed"
# (no checked text written).
#   usage: sh cyprun.sh name...
# No time limit: cyp's searches are bounded (cyp's
# README, "Deterministic bounds"), lia and nia behind lia_guard (a check of
# the goal's shape); lra, nra and Rocq's reduction end but have no bound.
# The copy gets a flags: line, so that the require: line written by xtext
# (Require Import XText.<file>) finds the compiled example files.
# Needs: the cyp library compiled in CYP_LIB, loading the lexicon (../lexicon,
# before elpi/text.elpi; default ../cyp/vernac:
# rocq c -Q . CypV Cyp.v) and the driver built (in ../cyp: dune build
# ./bin/cyp.exe).

here=$(cd "$(dirname "$0")" && pwd)
CYP=${CYP:-$here/../cyp/_build/default/bin/cyp.exe}
CYP_LIB=${CYP_LIB:-$here/../cyp/vernac}
export CYP_LIB
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)"
# the memory allowed per text, in GB: 8 by default, so that runs in
# parallel fit on the machine; a hard text may get more (CYP_MEMORY_GB=16),
# one such run at a time (some texts went over 16 GB)
mem_gb=${CYP_MEMORY_GB:-8}
ulimit -v $((mem_gb * 1000000))
cd "$here/cyp-check" || exit 1
for f in "$@"; do
  mkdir -p "$(dirname "$f")"
  sed -e "s|^by: |flags: -R $here XText\nby: |" "../examples/$f.md" > "$f.md"
  rm -f "$f.checked.md" "$f.cyp.json" "$f.cyp-cache"
  s=$(date +%s)
  nice -n 19 "$CYP" "$f.md" > "$f.out" 2>&1
  t=$(( $(date +%s) - s ))
  g=$f.checked.md
  if [ -f "$g" ]; then
    printf "%s\t%s\t%s\t%s\t%s\n" "$f" "$t" "$(grep -c '^ *- ✅' "$g")" "$(grep -c '^ *- ❌' "$g")" "$(grep -c '^ *- ▫️' "$g")"
  else
    printf "%s\t%s\tfailed\n" "$f" "$t"
  fi
done
