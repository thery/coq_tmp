#!/bin/sh
# Checks that the tutorial (../TUTORIAL.md, ../TUTORIAL-2.md) is still true: runs the program
# cyp on every text chNN_*.md, and Rocq on every chapter file chNN_*.v,
# and compares what they print and the checked texts they write with the
# expected outputs in expected/.
#   usage: sh check.sh            compare (exit 1 on a difference)
#          sh check.sh --update   rewrite expected/ from this run
# The chapter files name their texts "cyp-tutorial/chNN_*.md", as in
# rocq-web, where Rocq runs from the root of the files: the run copies this
# directory to TMP/cyp-tutorial and runs Rocq from TMP.
# Needs the cyp library built (cyp/README.md) and the driver
# cyp/_build/default/bin/cyp.exe (or CYP_EXE).
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)"
export CYP_LIB="$root/cyp/vernac"
exe=${CYP_EXE:-$root/cyp/_build/default/bin/cyp.exe}
ulimit -v 8000000
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
work=$tmp/cyp-tutorial
mkdir -p "$work" "$tmp/out/cyp" "$tmp/out/rocq"
cp "$here"/ch*.md "$here"/ch*.v "$work"/
rm -f "$work"/*.checked.md "$work"/*.cyp.json
# the absolute paths of this run, which differ from run to run
clean() { sed -e "s|$tmp/||g"; }

# 1. the program cyp on each text
cd "$work" || exit 2
for md in ch*.md; do
  n=${md%.md}
  { nice "$exe" "$md" 2>&1; echo "exit $?"; } | clean > "$tmp/out/cyp/$n.out"
  [ -f "$n.checked.md" ] && mv "$n.checked.md" "$tmp/out/cyp/"
  rm -f "$n.cyp.json"
done
{ nice "$exe" --conditions ch07_structure.md 2>&1; echo "exit $?"; } | clean > "$tmp/out/cyp/ch07_structure.conditions.out"

# 2. Rocq on each chapter file, from the parent directory, as in rocq-web
cd "$tmp" || exit 2
for v in cyp-tutorial/ch*.v; do
  n=$(basename "$v" .v)
  case $n in *_rules) continue ;; esac
  { nice rocq c -Q "$root/cyp/vernac" CypV -Q "$root/lexicon" Lexicon \
      -Q "$root/prooftext" ProofText "$v" 2>&1; echo "exit $?"; } |
    clean > "$tmp/out/rocq/$n.out"
done
for c in "$work"/*.checked.md; do [ -f "$c" ] && mv "$c" "$tmp/out/rocq/"; done

# 3. the rules of chapter 9 are in ch09_words.v as they are in their file
sed -n '/^(\* rules: begin \*)$/,/^(\* rules: end \*)$/p' "$here/ch09_words.v" |
  sed '1d;$d' | cmp -s - "$here/ch09_words_rules.v" ||
  { echo "check.sh: ch09_words.v does not hold ch09_words_rules.v"; exit 1; }

# 4. each block of ../TUTORIAL*.md after a line "<!-- tutorial: PATH -->" is
#    an exact excerpt (consecutive whole lines) of PATH, relative to here
mkdir -p "$tmp/blocks"
awk -v d="$tmp/blocks" '
  /^<!-- tutorial: .* -->$/ { p = $3; next }
  p != "" && /^```/ && !inb { inb = 1; k++; print p > (d "/list"); f = d "/" k; printf "" > f; next }
  inb && /^```$/ { inb = 0; p = ""; close(f); next }
  inb { print > f }
' "$here/../TUTORIAL.md" "$here/../TUTORIAL-2.md"
k=0; bad=0
while read -r p; do
  k=$((k + 1))
  awk 'NR == FNR { b[++nb] = $0; next } { f[++nf] = $0 }
       END { for (i = 1; i + nb - 1 <= nf; i++) { ok = 1
               for (j = 1; j <= nb; j++) if (f[i + j - 1] != b[j]) { ok = 0; break }
               if (ok) exit 0 }
             exit 1 }' "$tmp/blocks/$k" "$here/$p" ||
    { echo "check.sh: block $k of the tutorial is no excerpt of $p"; bad=1; }
done < "$tmp/blocks/list"
[ $bad = 0 ] || exit 1
echo "check.sh: the $k blocks of the tutorial are excerpts of their files"

if [ "$1" = "--update" ]; then
  rm -rf "$here/expected"; cp -r "$tmp/out" "$here/expected"
  echo "check.sh: expected/ rewritten"; exit 0
fi
if diff -r "$here/expected" "$tmp/out"; then
  echo "check.sh: all $(ls "$tmp"/out/cyp/*.out "$tmp"/out/rocq/*.out | wc -l) runs as expected"
else
  echo "check.sh: differences (above)"; exit 1
fi
