#!/bin/sh
# Print the tables of the lexicon as Markdown (for README.md): per
# language, the writer's phrases by use (role, side) and the phrases that
# are only read.   usage: sh tables.sh > tables.md
cd "$(dirname "$0")" || exit 1
name() { case $1 in en) echo English;; fr) echo French;; it) echo Italian;; de) echo German;;
  nl) echo Dutch;; ru) echo Russian;; zh) echo Chinese;; ar) echo Arabic;; ko) echo Korean;;
  la) echo Latin;; *) echo "$1";; esac; }
for f in lang_*.elpi; do
  l=${f#lang_}; l=${l%.elpi}
  echo; echo "### $(name $l) ($l)"; echo
  echo "| use | phrase | role | side |"; echo "|---|---|---|---|"
  grep -o 'write-role "'$l'" "[^"]*" "[^"]*" [a-z]*' $f | while IFS='"' read -r a b c u e p g; do
    r=$(echo $g | tr -d ' '); s=before; grep -q "phrase-after \"$l\" \"$p\"" $f && s=after
    echo "| $u | $p | ${r#r} | $s |"; done
  grep -o 'write-word "'$l'" "[^"]*" "[^"]*"' $f | while IFS='"' read -r a b c u e p g; do
    s=before; grep -q "phrase-after \"$l\" \"$p\"" $f && s=after
    echo "| $u | $p | (none) | $s |"; done
  rd=$(grep -o 'phrase "'$l'" "[^"]*" r[a-z]*' $f | sed 's/^phrase "[a-z]*" "\([^"]*\)" r\([a-z]*\)$/\1 (\2)/' | paste -sd ';' | sed 's/;/; /g')
  echo; echo "Read only: $rd."
  x=$(grep -h '^\(clitic\|punctuation\|unspaced\)' $f | tr '\n' ' '); [ -n "$x" ] && { echo; echo "Writing system: \`$x\`"; }
done
