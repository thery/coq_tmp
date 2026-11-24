#!/bin/bash
# convert_check.sh: the round trips of the converter (Convert.v,
# convert.elpi) on the public proof texts, checked with cyp.
#   usage: bash convert_check.sh [-j N]      (N cyp runs at a time, default 4)
# For each text T (in the style S, structured if it has a list item, else
# free; O the other style):
#   C1 = T in the style O, C2 = C1 back in the style S, C3 = C2 in O;
#   - back: C2 is T exactly, or up to the line breaks inside paragraphs
#     (the converter fills again a paragraph whose lines are longer than
#     the width), or differs (the difference is in the log);
#   - again: C3 is C1 (the converter's own text, converted back and
#     forth), exactly or up to the line breaks;
#   - trees: cyp's tree of T (NAME.cyp.json: the steps, their ids,
#     statuses, formulas and messages, and the justification words, the
#     line numbers left out: the fields first and last, and "line N" in
#     the messages) is that of C1 and of C2.
# Then the twins written by hand in the other style (../proposal/examples,
# ../cyp/tutorial/ch08_*): the converted text compared with its twin.
# Prints the counts; the details in the log (the last line says where).
# Needs: the cyp library compiled and the driver built (../cyp/README.md),
# xtext's libraries compiled (cd ../xtext && make), the switch elpi5.
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
jobs=4; [ "${1:-}" = -j ] && jobs=$2
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)"
export CYP_LIB="$root/cyp/vernac"
exe=${CYP_EXE:-$root/cyp/_build/default/bin/cyp.exe}
[ -x "$exe" ] || { echo "convert_check: no driver $exe (cd ../cyp && dune build ./bin/cyp.exe)"; exit 2; }
ulimit -v 8000000
tmp=$(mktemp -d) || exit 2
log=$tmp/convert_check.log
Q="-Q $root/lexicon Lexicon -Q $here ProofText"
(cd "$here" && rocq c $Q Convert.v) || exit 1

# the texts: their paths from the root
(cd "$root" && ls cyp/examples/*.md cyp/tutorial/ch*.md cyp/vernac/*.md xtext/examples/*.md \
   xtext/examples/*/*.md proposal/examples/*.free.md proposal/examples/*.structured.md) |
  grep -v -e '\.checked\.md$' -e '/README\.md$' -e '^xtext/examples/exp_' > "$tmp/texts"
n=$(wc -l < "$tmp/texts")

# each variant (orig, c1, c2, c3) in a copy of the directories of the texts,
# so that the files a header names (rules:) are there; xtext's texts get a
# flags line for its libraries (as ../xtext/cyprun.sh)
for v in orig c1 c2 c3; do
  for d in $(xargs -n1 dirname < "$tmp/texts" | sort -u); do mkdir -p "$tmp/$v/$d"; cp -r "$root/$d"/. "$tmp/$v/$d"/; done
  find "$tmp/$v" -name '*.checked.md' -o -name '*.cyp.json' | xargs rm -f
done
while read -r t; do
  case $t in xtext/*|proposal/*) sed -i "s|^by: |flags: -R $root/xtext XText\nby: |" "$tmp/orig/$t" ;; esac
done < "$tmp/texts"

style() { if grep -q '^ *[-*] ' "$1"; then echo structured; else echo free; fi; }
other() { if [ "$1" = free ]; then echo structured; else echo free; fi; }

# the conversions, in one Rocq file per step
step() {  # [step FROM TO]: each text of FROM converted into TO, in the other style (of the original for c2)
  { echo "From ProofText Require Import Convert."
    while read -r t; do
      s=$(style "$tmp/orig/$t"); o=$(other "$s")
      case $2 in c2) to=$s ;; *) to=$o ;; esac
      echo "Convert \"$tmp/$1/$t\" to \"$tmp/$2/$t\" as $to."
    done < "$tmp/texts"; } > "$tmp/step_$2.v"
  (cd "$tmp" && rocq c $Q "step_$2.v") > "$tmp/step_$2.log" 2>&1 || { echo "convert_check: FAILED: $2 ($tmp/step_$2.log)"; exit 1; }
}
step orig c1; step c1 c2; step c2 c3

# up to the line breaks inside a paragraph: each paragraph, item or fence
# on one line, its lines joined by a space
unbroken() {
  awk 'function out() { if (buf != "") print buf; buf = "" }
       /^[ \t]*$/ { out(); print ""; next }
       /^ *([-*] |:::)/ { out(); buf = $0; if ($0 ~ /^ *:::/) { out() } next }
       { s = $0; sub(/^ +/, "", s); if (buf == "") buf = $0; else buf = buf " " s }
       END { out() }' "$1"
}

# cyp on the variants that need it
: > "$tmp/runs"
while read -r t; do
  echo "orig/$t" >> "$tmp/runs"; echo "c1/$t" >> "$tmp/runs"
  cmp -s "$tmp/orig/$t" "$tmp/c2/$t" || echo "c2/$t" >> "$tmp/runs"
done < "$tmp/texts"
export tmp exe
xargs -P "$jobs" -I{} sh -c 'cd "$tmp/$(dirname {})" && nice -n 19 "$exe" "$(basename {})" > "$(basename {} .md).out" 2>&1; true' < "$tmp/runs"

tree() { tr -d '\n' < "$1" | sed 's/"first":[0-9]*,"last":[0-9]*,//g; s/line [0-9][0-9]*/line N/g; s/"justifications":.*//'; echo; grep -o '"word":"[^"]*","meaning":"[^"]*"' "$1"; }
same-tree() {  # [same-tree T V]: the tree of the variant V of T is that of T
  local x=$tmp/orig/${1%.md}.cyp.json y=$tmp/$2/${1%.md}.cyp.json
  [ -f "$x" ] && [ -f "$y" ] && cmp -s <(tree "$x") <(tree "$y")
}

exact=0; breaks=0; differ=0; again=0; again_breaks=0; trees=0; notree=0; badtree=0
while read -r t; do
  s=$(style "$tmp/orig/$t")
  if cmp -s "$tmp/orig/$t" "$tmp/c2/$t"; then back=exact; exact=$((exact + 1))
  elif cmp -s <(unbroken "$tmp/orig/$t") <(unbroken "$tmp/c2/$t"); then back=breaks; breaks=$((breaks + 1))
  else back=differs; differ=$((differ + 1))
       { echo "== $t ($s): back differs"; diff "$tmp/orig/$t" "$tmp/c2/$t"; } >> "$log"; fi
  if cmp -s "$tmp/c1/$t" "$tmp/c3/$t"; then a=same; again=$((again + 1))
  elif cmp -s <(unbroken "$tmp/c1/$t") <(unbroken "$tmp/c3/$t"); then a=breaks; again_breaks=$((again_breaks + 1))
  else a=differs; { echo "== $t: again differs"; diff "$tmp/c1/$t" "$tmp/c3/$t"; } >> "$log"; fi
  if [ ! -f "$tmp/orig/${t%.md}.cyp.json" ]; then tr=none; notree=$((notree + 1))
  elif same-tree "$t" c1 && { [ "$back" = exact ] || same-tree "$t" c2; }; then tr=same; trees=$((trees + 1))
  else tr=DIFFERENT; badtree=$((badtree + 1)); echo "== $t: the trees differ" >> "$log"; fi
  echo "$t $s back:$back again:$a tree:$tr" >> "$tmp/table"
done < "$tmp/texts"
cat "$tmp/table" >> "$log"
nf=$(grep -c ' free back' "$tmp/table"); ns=$((n - nf))
echo "convert_check: $n texts ($ns structured, $nf free)"
echo "  back in their style: $exact exact, $breaks up to line breaks, $differ different"
echo "  converted again (C3 = C1): $again exact, $again_breaks up to line breaks, $((n - again - again_breaks)) different"
echo "  trees: $trees the same, $badtree different, $notree with no tree (cyp wrote no JSON)"

# the twins written by hand
twins="proposal/examples/praeclarum proposal/examples/square_pos proposal/examples/Trans_Inv proposal/examples/xtext_praeclarum proposal/examples/exp_pos"
for b in $twins; do
  for p in "free structured" "structured free"; do
    set -- $p
    c=$tmp/c1/$b.$1.md; w=$tmp/orig/$b.$2.md
    if cmp -s <(sed '/^# /,$!d' "$c") <(sed '/^# /,$!d' "$w"); then r=same
    elif cmp -s <(unbroken "$c" | sed '/^# /,$!d') <(unbroken "$w" | sed '/^# /,$!d'); then r="same up to line breaks"
    else r="$(diff <(sed '/^# /,$!d' "$c") <(sed '/^# /,$!d' "$w") | grep -c '^[<>]') lines differ"
         { echo "== twin $b.$2.md vs $b.$1.md converted"; diff "$w" "$c"; } >> "$log"; fi
    echo "  twin: $b.$1.md converted to $2: $r"
  done
done
c=$tmp/c1/cyp/tutorial/ch08_free.md; w=$tmp/orig/cyp/tutorial/ch08_structured.md
echo "  twin: cyp/tutorial/ch08_free.md converted to structured: $(diff <(sed '/^# /,$!d' "$c") <(sed '/^# /,$!d' "$w") | grep -c '^[<>]') lines differ"
c=$tmp/c1/cyp/tutorial/ch08_structured.md; w=$tmp/orig/cyp/tutorial/ch08_free.md
echo "  twin: cyp/tutorial/ch08_structured.md converted to free: $(diff <(sed '/^# /,$!d' "$c") <(sed '/^# /,$!d' "$w") | grep -c '^[<>]') lines differ"
echo "convert_check: details in $log (the texts in $tmp)"
[ $badtree = 0 ]
