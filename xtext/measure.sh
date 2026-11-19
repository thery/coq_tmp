#!/bin/sh
# Compile one example file and print, for each ExtractText, the output file,
# its generation time (s), its number of list items and its size (chars).
# usage: sh measure.sh file.v [extra rocq flags]
f=$1; shift
out=$(rocq c -R . XText -Q ../lexicon Lexicon -Q ../prooftext ProofText "$@" "$f" 2>&1)
echo "$out" | grep "Finished transaction" | sed 's/Finished transaction in \([0-9.]*\) secs.*/\1/' > /tmp/xtext_times.$$
grep '^Time ExtractText' "$f" | sed 's/.*to "\(.*\)"\./\1/' > /tmp/xtext_files.$$
paste /tmp/xtext_files.$$ /tmp/xtext_times.$$ | while read md t; do
  printf "%s\t%s\t%s\t%s\n" "$(basename "$md" .md)" "$t" "$(grep -c '^ *- ' "$md")" "$(wc -c < "$md")"
done
rm -f /tmp/xtext_times.$$ /tmp/xtext_files.$$
