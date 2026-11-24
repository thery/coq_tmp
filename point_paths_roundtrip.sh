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
#      parentheses and a final %scope.  A tag on a let (or a let '(..)
#      match) whose text Rocq-Elpi prints in another style (let (x, _) :=
#      s for let 'exist _ x _ := s, nested lets for a nested pattern,
#      (t : T) for let k := t in k) is RT-STYLE: listed, not a failure.
#   Also, for each part, the binder names (of a used variable, under a
#   printed binder) that no tag names are listed (RT-UNTAGGED, not a
#   failure: a printer limit, the names of exists x, .. and of mathcomp's
#   notations).  The cases are point_paths_cases.v and, when mathcomp is
#   installed, point_paths_cases_mathcomp.v.
#   usage: bash point_paths_roundtrip.sh   (in the opam switch of the Rocq
#          that tags the paths, e.g. opam exec --switch=vsrocq-pathtags --;
#          exit 1 on a mismatch or an error).  The .v files it needs are
#          compiled in a scratch copy, under 8 GB of virtual memory.
here=$(cd "$(dirname "$0")" && pwd)
me=point_paths_roundtrip
tmp=$(mktemp -d) || exit 2
[ -n "$RT_KEEP" ] && echo "$me: kept in $tmp" || trap 'rm -rf "$tmp"' EXIT
ulimit -v 8000000
cp "$here"/pbp.v "$here"/pbp_select.v "$here"/point_actions.v "$here"/point_paths_cases.v "$here"/point_paths_cases_mathcomp.v "$tmp"/
cd "$tmp" || exit 2
for f in pbp pbp_select point_actions; do
  rocq c -R . coq_tmp $f.v > $f.out 2>&1 || { echo "$me: $f.v does not compile:"; cat $f.out; exit 2; }
done
# the parser of the tagged goals (Show): one line "case|hyp|path|text" per
# tag (hyp: - for the conclusion; the innermost tag closes first)
cat > parse.awk <<'AWK'
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
/^@@CASE / { if (inconcl) flush_part(buf, "-"); cs = $2; inconcl = 0; hyp = ""; buf = ""; next }
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
# a hypothesis whose type is printed on the next lines: "  H :"
/^  [^ ].* :$/ {
  if (hyp != "") flush_part(buf, hyp)
  names = $0; sub(/^  /, "", names); sub(/ :$/, "", names)
  if (names ~ / := /) { hyp = ""; next }
  split(names, ns, ", "); hyp = ns[1]; buf = ""; next }
/^  [^ ].* := / { if (hyp != "") flush_part(buf, hyp); hyp = ""; next }
hyp != "" && /^ / { buf = buf " " $0; next }
END { if (inconcl) flush_part(buf, "-") }
AWK
status=0
# [roundtrip F] the round trip of the goals of F
roundtrip() {
  f=$1; b=${f%.v}
  # 1. the tagged goals
  awk '
  /^From coq_tmp Require Import point_actions\.$/ { print; print "Set Printing Subterm Paths."; next }
  /^elpi point_paths_check\.$/ { n++; printf "idtac \"@@CASE %d\".\nShow.\n", n; next }
  { print }' $f > ${b}_show.v
  if ! rocq c -R . coq_tmp ${b}_show.v > $b.show.out 2> $b.show.err; then
    echo "$me: the copy of $f with Show does not compile:"; cat $b.show.err; status=2; return
  fi
  # 2. the tags
  awk -f parse.awk $b.show.out > $b.tags
  ntags=$(wc -l < $b.tags)
  # 3. the check of each tag, and of the names of each part
  awk -v tags=$b.tags '
  function esc(s) { gsub(/"/, "\"\"", s); return s }
  BEGIN {
    while ((getline l < tags) > 0) {
      i = index(l, "|"); c = substr(l, 1, i - 1); l = substr(l, i + 1)
      i = index(l, "|"); h = substr(l, 1, i - 1); l = substr(l, i + 1)
      i = index(l, "|"); p = substr(l, 1, i - 1); t = substr(l, i + 1)
      if (h == "-") line = sprintf("elpi point_path_text \"%s\" \"%s\" \"%s\".", c, p, esc(t))
      else line = sprintf("elpi point_path_text \"%s\" \"%s\" \"%s\" \"%s\".", c, esc(h), p, esc(t))
      chk[c] = chk[c] line "\n"
      k = c SUBSEP h; if (!(k in parts)) { parts[k] = 1; order[c] = order[c] SUBSEP h }
      paths[k] = paths[k] " \"" p "\""
    }
  }
  /^elpi point_paths_check\.$/ {
    n++; printf "%s", chk[n]
    m = split(order[n], hs, SUBSEP)
    for (j = 2; j <= m; j++) {
      h = hs[j]; w = (h == "-") ? "|-" : h
      printf "elpi point_paths_untagged \"%s\" \"%s\"%s.\n", n, esc(w), paths[n SUBSEP h]
    }
    next }
  { print }' $f > ${b}_check.v
  if ! rocq c -R . coq_tmp ${b}_check.v > $b.check.out 2> $b.check.err; then
    echo "$me: the copy of $f with the checks does not compile:"; cat $b.check.err; status=2; return
  fi
  ok=$(grep -c '^RT-OK' $b.check.out)
  bad=$(grep -c '^RT-MISMATCH' $b.check.out)
  skip=$(grep -c '^RT-SKIP' $b.check.out)
  style=$(grep -c '^RT-STYLE' $b.check.out)
  untagged=$(grep -c '^RT-UNTAGGED' $b.check.out)
  ncases=$(grep -c '^elpi point_paths_check\.$' $f)
  echo "$me: $ntags tags in the $ncases goals of $f: $ok ok, $bad mismatches, $style lets printed in another style by Rocq-Elpi, $skip skipped (section variables); $untagged binder names not tagged"
  [ "$style" -ne 0 ] && { echo "$me: the lets printed in another style (not failures):"; grep '^RT-STYLE' $b.check.out; }
  [ "$untagged" -ne 0 ] && { echo "$me: the binder names that no tag names (not failures: a printer limit):"; grep '^RT-UNTAGGED' $b.check.out; }
  if [ "$bad" -ne 0 ]; then
    echo "$me: the mismatches (case, part, path, the tag's text, the text at the path):"
    grep '^RT-MISMATCH' $b.check.out; status=1
  fi
  [ $((ok + skip + style + bad)) -eq "$ntags" ] || { echo "$me: $ntags tags but $((ok + skip + style + bad)) checks"; status=1; }
}
roundtrip point_paths_cases.v
if echo 'From mathcomp Require Import ssreflect.' > mc_probe.v && rocq c mc_probe.v > /dev/null 2>&1; then
  roundtrip point_paths_cases_mathcomp.v
else
  echo "$me: mathcomp is not installed: point_paths_cases_mathcomp.v is not checked"
fi
exit $status
