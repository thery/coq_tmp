#!/bin/sh
# The results of probe.sh as one line per condition and candidate:
#   text  condition  tactic  OK|KO  seconds
# (a candidate stopped by its time limit has no time line: its seconds are
# the limit, 2).
#   usage: sh table.sh OUTDIR/*.log
for f in "$@"; do
  awk -v text="$(basename "$f" .log)" '
    /^COND / { c = $2; sub(/%pstring/, "", c); gsub(/"/, "", c) }
    /^T /    { t = $2; s = 2 }
    /^Tactic call ran for/ { s = $5 }
    /^OK$|^KO$/ { print text "\t" c "\t" t "\t" $1 "\t" s }' "$f"
done
