#!/bin/bash
# The round trip of the subterm paths: on the goals of point_paths_cases.v,
# every tag P (text T) that Rocq's printer puts on a printed subterm under
# Set Printing Subterm Paths must name, for point_run_path, a subterm (or a
# binder name) of the goal that prints as T.
#   1. A copy of point_paths_cases.v where each [elpi point_paths_check.]
#      is [idtac "@@CASE n". Show.], with Set Printing Subterm Paths, is
#      compiled: the goals are printed with their tags, <P>text</P> (<>
#      .. </> the whole part).
#   2. The tags of each part (the conclusion, the type of each hypothesis;
#      not the local definitions, which point_run_path does not take) are
#      read (awk: the innermost tag closes first).
#   3. A second copy where each [elpi point_paths_check.] is the list of
#      [elpi point_path_text "n" ["H"] "P" "T".] of its goal is compiled
#      (without the tags): each prints RT-OK, or RT-MISMATCH with the text
#      at the path.  The texts are compared without blanks, outer
#      parentheses and a final %scope.
#   usage: bash point_paths_roundtrip.sh   (in the opam switch of the Rocq
#          that tags the paths, e.g. opam exec --switch=vsrocq-pathtags --;
#          exit 1 on a mismatch or an error).  The .v files it needs are
#          compiled in a scratch copy, under 8 GB of virtual memory.
here=$(cd "$(dirname "$0")" && pwd)
me=point_paths_roundtrip
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
ulimit -v 8000000
cp "$here"/pbp.v "$here"/pbp_select.v "$here"/point_actions.v "$here"/point_paths_cases.v "$tmp"/
cd "$tmp" || exit 2
for f in pbp pbp_select point_actions; do
  rocq c -R . coq_tmp $f.v > $f.out 2>&1 || { echo "$me: $f.v does not compile:"; cat $f.out; exit 2; }
done
# 1. the tagged goals
awk '
/^From coq_tmp Require Import point_actions\.$/ { print; print "Set Printing Subterm Paths."; next }
/^elpi point_paths_check\.$/ { n++; printf "idtac \"@@CASE %d\".\nShow.\n", n; next }
{ print }' point_paths_cases.v > rt_show.v
if ! rocq c -R . coq_tmp rt_show.v > show.out 2> show.err; then
  echo "$me: the copy with Show does not compile:"; cat show.err; exit 2
fi
# 2. the tags: one line "case|hyp|path|text" per tag (hyp: - for the
#    conclusion)
awk '
function flush_part(s, hyp,    i, c, rest, m, path, stack, pos, depth, plain, t) {
  depth = 0; plain = ""
  while (length(s) > 0) {
    if (match(s, /^<\/?[0-9.]*>/)) {
      m = substr(s, 1, RLENGTH); rest = substr(s, RLENGTH + 1)
      if (m == "<>" && depth == 0) { depth = 1; stack[1] = ""; pos[1] = length(plain); s = rest; continue }
      if (m == "</>" && depth == 1 && stack[1] == "") {
        printf "%s|%s||%s\n", cs, hyp, plain; depth = 0; s = rest; continue }
      if (m ~ /^<[0-9.]+>$/ && depth > 0) {
        depth++; stack[depth] = substr(m, 2, length(m) - 2); pos[depth] = length(plain); s = rest; continue }
      if (m ~ /^<\/[0-9.]+>$/ && depth > 1 && substr(m, 3, length(m) - 3) == stack[depth]) {
        t = substr(plain, pos[depth] + 1); printf "%s|%s|%s|%s\n", cs, hyp, stack[depth], t
        depth--; s = rest; continue }
    }
    plain = plain substr(s, 1, 1); s = substr(s, 2)
  }
}
/^@@CASE / { cs = $2; inconcl = 0; hyp = ""; buf = ""; next }
cs == "" { next }
/^  =+$/ { if (hyp != "") flush_part(buf, hyp); hyp = ""; inconcl = 1; buf = ""; next }
inconcl {
  if ($0 ~ /^ *$/ || $0 ~ /^[^ ]/) { flush_part(buf, "-"); inconcl = 0; cs = ""; next }
  buf = buf " " $0; next }
/^  [^ ].* : <>/ {
  if (hyp != "") flush_part(buf, hyp)
  line = $0; sub(/^  /, "", line)
  names = line; sub(/ : <>.*/, "", names)
  if (names ~ / := /) { hyp = ""; next }       # a local definition
  split(names, ns, ", "); hyp = ns[1]
  buf = substr(line, index(line, " : <>") + 3); next }
/^  [^ ].* := / { if (hyp != "") flush_part(buf, hyp); hyp = ""; next }
hyp != "" && /^ / { buf = buf " " $0; next }
END { if (inconcl) flush_part(buf, "-") }
' show.out > tags
ntags=$(wc -l < tags)
# 3. the check of each tag
awk -v tags=tags '
function esc(s) { gsub(/"/, "\"\"", s); return s }
BEGIN {
  while ((getline l < tags) > 0) {
    i = index(l, "|"); c = substr(l, 1, i - 1); l = substr(l, i + 1)
    i = index(l, "|"); h = substr(l, 1, i - 1); l = substr(l, i + 1)
    i = index(l, "|"); p = substr(l, 1, i - 1); t = substr(l, i + 1)
    if (h == "-") line = sprintf("elpi point_path_text \"%s\" \"%s\" \"%s\".", c, p, esc(t))
    else line = sprintf("elpi point_path_text \"%s\" \"%s\" \"%s\" \"%s\".", c, esc(h), p, esc(t))
    chk[c] = chk[c] line "\n"
  }
}
/^elpi point_paths_check\.$/ { n++; printf "%s", chk[n]; next }
{ print }' point_paths_cases.v > rt_check.v
if ! rocq c -R . coq_tmp rt_check.v > check.out 2> check.err; then
  echo "$me: the copy with the checks does not compile:"; cat check.err; exit 2
fi
ok=$(grep -c '^RT-OK' check.out)
bad=$(grep -c '^RT-MISMATCH' check.out)
skip=$(grep -c '^RT-SKIP' check.out)
ncases=$(grep -c '^elpi point_paths_check\.$' point_paths_cases.v)
echo "$me: $ntags tags in the $ncases goals of point_paths_cases.v: $ok ok, $bad mismatches, $skip skipped (section variables)"
if [ "$bad" -ne 0 ]; then
  echo "$me: the mismatches (case, part, path, the tag's text, the text at the path):"
  grep '^RT-MISMATCH' check.out
  exit 1
fi
[ $((ok + skip)) -eq "$ntags" ] || { echo "$me: $ntags tags but $((ok + skip)) checks"; exit 1; }
exit 0
