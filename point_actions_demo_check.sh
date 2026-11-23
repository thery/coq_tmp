#!/bin/sh
# Checks that point_actions_demo.v is still true.
# 1. Each line that a button writes: in the demo, a comment
#      (* click "Name" on SEL *)
#    is followed by the line of the action Name for the selection SEL (run,
#    or shown as a comment (* line *)).  The check writes a copy of the demo
#    where each such comment is followed by
#      elpi point_run_expect "Name" "line" "" SEL.
#    and compiles it: point_run must give that very line, on the goal of
#    the demo at that point, without widening the selection.
# 2. Each excerpt: a comment that starts with a line
#      (* FILE, line N:      or      (* FILE, lines N-M:
#    and ends with a line *) holds exactly the lines N to M of FILE.
#   usage: sh point_actions_demo_check.sh     (from anywhere; exit 1 on a
#          difference).  Needs pbp.v, pbp_select.v, point_actions.v
#          compiled, with the rocq of the current opam switch.
here=$(cd "$(dirname "$0")" && pwd)
demo=$here/point_actions_demo.v
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
ulimit -v 8000000
status=0

# ---- 1. the lines of the actions ----
awk '
function esc(s) { gsub(/"/, "\"\"", s); return s }
/^\(\* click ".*" on [^*]* \*\)$/ {
  print
  s = $0; sub(/^\(\* click "/, "", s)
  i = index(s, "\" on "); name = substr(s, 1, i - 1)
  sel = substr(s, i + 5); sub(/ \*\)$/, "", sel)
  if ((getline nxt) <= 0) { print "no line after the last click" > "/dev/stderr"; exit 1 }
  line = nxt
  if (line ~ /^\(\* .* \*\)$/) { sub(/^\(\* /, "", line); sub(/ \*\)$/, "", line) }
  printf "elpi point_run_expect \"%s\" \"%s\" \"\" %s.\n", esc(name), esc(line), sel
  print nxt
  n++
  next
}
{ print }
END { print "(* " n " clicks checked *)"; print n > "/dev/stderr" }
' "$demo" > "$tmp/demo_run.v" 2> "$tmp/count" || exit 2
clicks=$(cat "$tmp/count")
if [ "$clicks" -eq 0 ]; then echo "point_actions_demo_check: no click found"; exit 1; fi
if (cd "$tmp" && rocq c -R "$here" coq_tmp -R . demo_check demo_run.v > out 2>&1); then
  echo "point_actions_demo_check: the $clicks lines of the actions are the ones point_run gives"
else
  echo "point_actions_demo_check: a line is not the one point_run gives:"
  cat "$tmp/out"; status=1
fi

# ---- 2. the excerpts ----
awk -v dir="$here" -v tmp="$tmp" '
/^\(\* [A-Za-z_.]+\.v, lines? [0-9]+(-[0-9]+)?:$/ {
  s = $0; sub(/^\(\* /, "", s); sub(/:$/, "", s)
  i = index(s, ", line"); file = substr(s, 1, i - 1)
  r = substr(s, i + 6); sub(/^s? /, "", r)
  split(r, a, "-"); from = a[1]; to = (a[2] == "" ? a[1] : a[2])
  k++; out = tmp "/excerpt" k
  printf "%s %s %s %s\n", file, from, to, out > (tmp "/excerpts")
  inblock = 1; next
}
inblock && /^\*\)$/ { inblock = 0; close(out); next }
inblock { print > out }
' "$demo"
nb=0
while read -r file from to out; do
  nb=$((nb + 1))
  if ! sed -n "${from},${to}p" "$here/$file" | cmp -s - "$out"; then
    echo "point_actions_demo_check: the excerpt of $file, lines $from-$to, is not in $file:"
    sed -n "${from},${to}p" "$here/$file" | diff - "$out"; status=1
  fi
done < "$tmp/excerpts"
[ "$status" -eq 0 ] && echo "point_actions_demo_check: the $nb excerpts are verbatim in their files"
exit $status
