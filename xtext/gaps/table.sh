#!/bin/sh
# The results of probe.sh as one line per condition and candidate:
#   text  condition  tactic  OK|KO  seconds
# (a candidate stopped by its time limit has no time line: its seconds are
# the limit, 2).  The goals of the Proof block are in the order of the
# text, the order of cyp's lines 🔶 (condition NUMBER: goal); Ltac cannot
# read a goal's name, so the k-th line COND of Probe.v is the k-th of them.
#   usage: sh table.sh OUTDIR/*.log
for f in "$@"; do
  awk -v text="$(basename "$f" .log)" '
    $1 == "🔶" { n++; id[n] = $3; sub(/:$/, "", id[n]) }
    /^COND$/ { k++; c = id[k] }
    /^T /    { t = $2; s = 2 }
    /^Tactic call ran for/ { s = $5 }
    /^OK$|^KO$/ { print text "\t" c "\t" t "\t" $1 "\t" s }' "$f"
done
