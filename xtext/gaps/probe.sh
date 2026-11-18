#!/bin/sh
# Try the candidate tactics of Probe.v on the conditions that cyp leaves
# open in xtext's texts, one text at a time, under nice, with a time limit
# per text and at most CYP_MEMORY_GB (default 8) GB of memory.
#   usage: [PROBE=gap_final] sh probe.sh LIMIT OUTDIR text.md...
# BARE=1: every condition of the text, nothing tried by cyp (#[bare]).
# PROBE: the Ltac run on each open condition, gap_probe (the candidates,
# default) or gap_final (cyp_gap alone); CYP_LIB: the cyp library to use.
# For each text it writes OUTDIR/name.v (the header's require:, Cyp File
# in proof mode, gap_probe on every open condition) and OUTDIR/name.log,
# and prints: name, seconds, open conditions, maximum memory (KB).
lim=$1; out=$2; shift 2
here=$(cd "$(dirname "$0")" && pwd)
xt=$(cd "$here/.." && pwd)
lex=$(cd "$xt/../lexicon" && pwd)
CYP_LIB=${CYP_LIB:-$(cd "$xt/../cyp/vernac" && pwd)}
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi4 2>/dev/null)"
ulimit -v $(( ${CYP_MEMORY_GB:-8} * 1000000 ))
mkdir -p "$out/probe"; out=$(cd "$out" && pwd)
# Probe.v is compiled in OUTDIR/probe: xtext/ is mapped to XText, gaps/ with it
cp "$here/Probe.v" "$out/probe/"
(cd "$out/probe" && rocq c -Q "$CYP_LIB" CypV -Q "$lex" Lexicon -Q . Gaps Probe.v) || exit 1
for md in "$@"; do
  n=$(basename "$md" .md)
  cp "$md" "$out/$n.md"
  req=$(sed -n 's/^require: //p' "$md")
  sc=$(sed -n 's/^scope: //p' "$md")
  { echo "$req"
    echo "From CypV Require Import Cyp. From Gaps Require Import Probe."
    [ -n "$sc" ] && echo "Open Scope $sc."
    echo "${BARE:+#[bare] }Cyp File \"$out/$n.md\"."
    echo "Proof. all: (match goal with |- _ => ${PROBE:-gap_probe} end). Abort."; } > "$out/$n.v"
  s=$(date +%s)
  (cd "$out" && nice -n 19 timeout "$lim" /usr/bin/time -f "MAXRSS %M" rocq c -Q "$CYP_LIB" CypV -Q "$lex" Lexicon \
     -Q "$out/probe" Gaps -R "$xt" XText "$n.v" > "$n.log" 2>&1)
  printf "%s\t%s\t%s\t%s\n" "$n" "$(( $(date +%s) - s ))" "$(grep -c "^COND" "$out/$n.log")" "$(sed -n "s/^MAXRSS //p" "$out/$n.log")"
done
