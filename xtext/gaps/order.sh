#!/bin/sh
# From the table of table.sh: the candidates in a greedy order (each the
# one that closes most of the conditions still open), with the conditions
# closed so far; then, for a given order, the time per condition.
#   usage: sh order.sh TABLE              (the greedy order)
#          sh order.sh TABLE tac1 tac2 .. (the cost of that order)
t=$1; shift
if [ $# -eq 0 ]; then
  awk -F'\t' '
    { c = $1 "/" $2; cond[c] = 1; if ($4 == "OK") ok[c, $3] = 1; tac[$3] = 1 }
    END {
      n = 0; for (c in cond) n++
      left = n
      while (1) {
        best = ""; bn = 0
        for (k in tac) if (!used[k]) {
          m = 0; for (c in cond) if (!done[c] && ok[c, k]) m++
          if (m > bn) { bn = m; best = k } }
        if (bn == 0) break
        used[best] = 1; left -= bn
        for (c in cond) if (ok[c, best]) done[c] = 1
        printf "%s\t+%d\tclosed %d of %d\n", best, bn, n - left, n }
    }' "$t"
else
  awk -F'\t' -v order="$*" '
    BEGIN { m = split(order, o, " ") }
    { c = $1 "/" $2; cond[c] = 1; res[c, $3] = $4; sec[c, $3] = $5 }
    END {
      for (c in cond) {
        s = 0; closed = 0
        for (i = 1; i <= m; i++) {
          s += sec[c, o[i]]
          if (res[c, o[i]] == "OK") { closed = 1; break } }
        if (closed) { nc++; sc += s; if (s > mc) mc = s }
        else { nf++; sf += s; if (s > mf) mf = s } }
      printf "closed %d of %d; closed: mean %.3f s, max %.3f s; failed: mean %.3f s, max %.3f s\n",
        nc, nc + nf, nc ? sc / nc : 0, mc, nf ? sf / nf : 0, mf }' "$t"
fi
