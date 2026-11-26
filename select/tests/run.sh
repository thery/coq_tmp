#!/usr/bin/env bash
# Differential tests: the Elpi semantics of the patterns (subterm_select.v)
# against ssreflect's set.  Usage: select/tests/run.sh [corpus.v ...]
# (default: every corpus_*.v here), from anywhere; the library must be
# built (make select/subterm_select.vo in the root of coq_tmp).
#
# Stage 1 compiles each corpus file: its lines elpi diff_gen "Id". and
# elpi diff_cases "Id" ... print the cases (CASE lines: Id, hypothesis,
# the pattern as set writes it, the Elpi result).  Stage 2 is gen/<name>_ssr.v,
# the corpus where each such line is replaced by one line per case that
# runs set z := <pattern> and prints the positions of z (SSR lines); an
# elpi diff_gen or diff_cases line must be on one line.
# The two are joined on (Id, case number); the counts per category (the
# Id up to its first dot) and every disagreement are printed, and kept in
# gen/<name>.report.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
gen="$here/gen"
mkdir -p "$gen"
cd "$root"
files=("$@")
if [ ${#files[@]} -eq 0 ]; then files=("$here"/corpus_*.v); fi
total=0; agree=0; disagree=0
for f in "${files[@]}"; do
  name=$(basename "$f" .v)
  rel=select/tests/$(basename "$f")
  # the support file
  for s in diff_support random_gen; do if [ ! -f select/tests/$s.vo ] || [ select/tests/$s.v -nt select/tests/$s.vo ] || [ select/subterm_select.vo -nt select/tests/$s.vo ]; then
    rocq c -R . coq_tmp select/tests/$s.v || exit 1
  fi; done
  # stage 1
  if ! rocq c -R . coq_tmp "$rel" > "$gen/$name.stage1.log" 2>&1; then
    echo "$name: stage 1 failed (see gen/$name.stage1.log)"; continue
  fi
  grep -a "^CASE	" "$gen/$name.stage1.log" |
    awk -F'\t' '{n[$2]++; print $2 "\t" n[$2] "\t" $3 "\t" $4 "\t" $5}' > "$gen/$name.cases"
  # stage 2
  awk -F'\t' -v cases="$gen/$name.cases" '
    BEGIN { while ((getline l < cases) > 0) { split(l, a, "\t"); id = a[1];
              k[id]++; c[id, k[id]] = l } }
    /^elpi diff_(gen|cases|random) "/ {
      id = $0; sub(/^elpi diff_(gen|cases|random) "/, "", id); sub(/".*$/, "", id);
      for (i = 1; i <= k[id]; i++) {
        split(c[id, i], a, "\t"); n = a[2]; h = a[3]; pat = a[4];
        if (pat ~ /^\(in[ \t]/) { print "idtac \"SSR\t" id "\t" n "\tnot a c-pattern\"."; continue }
        err = "idtac \"SSR\t" id "\t" n "\terror\"";
        if (h == "")
          print "let G := match goal with |- ?G => G end in first [ assert_succeeds (set pattern_select_z := " pat "; elpi z_report \"" id "\" \"" n "\" ltac_term:(G)) | " err " ].";
        else
          print "let G := type of " h " in first [ assert_succeeds (set pattern_select_z := " pat " in " h "; elpi z_report \"" id "\" \"" n "\" ltac_term:(G) \"" h "\") | " err " ].";
      }
      next }
    { print }' "$f" > "$gen/${name}_ssr.v"
  rocq c -R . coq_tmp "select/tests/gen/${name}_ssr.v" > "$gen/$name.stage2.log" 2>&1
  status=$?
  grep -a "^SSR	" "$gen/$name.stage2.log" | awk -F'\t' '{print $2 "\t" $3 "\t" $4}' > "$gen/$name.ssr"
  # compare
  awk -F'\t' -v ssr="$gen/$name.ssr" -v name="$name" -v status="$status" '
    BEGIN { while ((getline l < ssr) > 0) { split(l, a, "\t"); s[a[1] "\t" a[2]] = a[3]; got[a[1] "\t" a[2]] = 1 } }
    { key = $1 "\t" $2; cat = $1; sub(/\..*$/, "", cat); tot[cat]++;
      if (!(key in got)) { miss[cat]++; dis[++nd] = "MISSING " $1 " #" $2 " " ($3 == "" ? "" : "in " $3 " ") $4 "  elpi: " $5; next }
      e = $5; r = s[key];
      if (e == "outside") { out[cat]++; outl[++no] = "OUTSIDE " $1 " #" $2 " " $4 "  ssreflect: [" r "]"; next }
      if (e == r) ok[cat]++; else { bad[cat]++; dis[++nd] = "DIFF " $1 " #" $2 " " ($3 == "" ? "" : "in " $3 " ") $4 "  elpi: [" e "]  ssreflect: [" r "]" } }
    END { if (status != 0) print name ": stage 2 stopped (status " status "), see gen/" name ".stage2.log";
          for (c in tot) printf "%s %s: %d cases, %d agree, %d disagree, %d outside, %d missing\n", name, c, tot[c], ok[c]+0, bad[c]+0, out[c]+0, miss[c]+0;
          for (i = 1; i <= nd; i++) print "  " dis[i];
          for (i = 1; i <= no; i++) print "  " outl[i] }' "$gen/$name.cases" | tee "$gen/$name.report"
done
