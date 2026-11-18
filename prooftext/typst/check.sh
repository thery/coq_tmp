#!/bin/sh
# Tests of the Typst back end: sh check.sh (from anywhere; nothing over a
# minute).  Each step prints "ok" or stops with the difference or error.
#
# 1. the texts of ../../xtext/examples-typst (written in Typst by xtext,
#    Explain foo to "foo.typ"): the Typst source that prooftext's reader
#    and write-typst give from the Markdown text (../../xtext/examples) is
#    the same, character for character;
# 2. texts checked by cyp (../../xtext/cyp-check/*.checked.md, with their
#    statuses): their Typst source is the expected one, tests/*.typ;
# 3. every Typst source of 1 and 2 compiles to a PDF with typst, without
#    errors or warnings (the PDFs are in tests/out/);
# 4. the round, when cyp is built (../../cyp/_build/default/bin/cyp.exe):
#    a text of xtext checked by cyp now, then its PDF.
#
# Needs: the opam switch elpi4, typst; for 1, xtext built (cd xtext && make).
# typst (a snap) reads and writes only under the home directory, not /tmp.
set -e
here=$(cd "$(dirname "$0")" && pwd)
prooftext=$(dirname "$here")
repo=$(dirname "$prooftext")
out=$here/tests/out
rm -rf "$out"; mkdir -p "$out"
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi4 2>/dev/null)" || true
ulimit -v 8000000

# Typst.vo up to date (pdf.sh compiles it when a source is newer)
sh "$prooftext/pdf.sh"

# [typst_of MD TYP]: the Typst source of the proof text MD, in TYP
typst_of() {
  printf 'From ProofText Require Import Typst.\nTypst "%s" to "%s".\n' "$1" "$2" > "$out/typst_of.v"
  nice rocq c -Q "$repo/lexicon" Lexicon -Q "$prooftext" ProofText "$out/typst_of.v" > "$out/typst_of.log" 2>&1 \
    || { cat "$out/typst_of.log"; exit 1; }
}

# [same NAME GOT WANTED]: the files GOT and WANTED are the same
same() {
  if cmp -s "$2" "$3"; then echo "ok   $1"
  else echo "FAIL $1: $2 differs from $3"; diff "$3" "$2" | head -20; exit 1; fi
}

# [compile TYP]: the PDF of TYP, in the directory of TYP; typst's warnings
# are failures too
compile() {
  nice typst compile --package-path "$here" "$1" "${1%.typ}.pdf" > "$out/typst.log" 2>&1 \
    || { cat "$out/typst.log"; exit 1; }
  if [ -s "$out/typst.log" ]; then cat "$out/typst.log"; exit 1; fi
  echo "ok   PDF ${1#$out/}"
}

echo "1. xtext's Typst = the Typst of xtext's Markdown, read back"
for typ in $(cd "$repo/xtext/examples-typst" && find . -name '*.typ' | sort); do
  name=${typ#./}; name=${name%.typ}
  mkdir -p "$out/$(dirname "$name")"
  typst_of "$repo/xtext/examples/$name.md" "$out/$name.typ"
  same "$name" "$out/$name.typ" "$repo/xtext/examples-typst/$name.typ"
done

echo "2. texts checked by cyp: the expected Typst"
for name in add_0_r half_le; do
  typst_of "$repo/xtext/cyp-check/$name.checked.md" "$out/$name.checked.typ"
  same "$name.checked" "$out/$name.checked.typ" "$here/tests/$name.checked.typ"
done

echo "3. the PDFs"
for typ in $(find "$out" -name '*.typ' | sort); do compile "$typ"; done

echo "4. the round: xtext's text, checked by cyp, then its PDF"
cyp=$repo/cyp/_build/default/bin/cyp.exe
if [ -x "$cyp" ] && [ -f "$repo/cyp/vernac/Cyp.vo" ]; then
  mkdir -p "$out/round"
  # the flags line lets the require line of the text find xtext's files
  sed -e "s|^by: |flags: -R $repo/xtext XText\nby: |" "$repo/xtext/examples/or_commut.md" > "$out/round/or_commut.md"
  (cd "$out/round" && CYP_LIB=$repo/cyp/vernac nice "$cyp" or_commut.md)
  typst_of "$out/round/or_commut.checked.md" "$out/round/or_commut.checked.typ"
  grep -q 'numbers: true' "$out/round/or_commut.checked.typ" \
    || { echo "FAIL round: no statuses in the Typst of the checked text"; exit 1; }
  compile "$out/round/or_commut.checked.typ"
else
  echo "skipped: cyp is not built (cd cyp && dune build ./bin/cyp.exe; cd vernac && rocq c ... Cyp.v)"
fi
echo "all ok"
