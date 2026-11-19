#!/bin/sh
# Tests of the Typst back end: sh check.sh (from anywhere; about a minute and a half).
# Each step prints "ok" or stops with the difference or error.
#
# 1. the texts of ../../xtext/examples-typst (written in Typst by xtext,
#    ExtractText foo to "foo.typ"): the Typst source that prooftext's reader
#    and write-typst give from the Markdown text (../../xtext/examples) is
#    the same, character for character;
# 2. texts checked by cyp (../../xtext/cyp-check/*.checked.md, with their
#    statuses; their flags line left out, the load path of xtext given by
#    pdf.sh --flags): their Typst source is the expected one, tests/*.typ;
# 3. the formulas as mathematics: the unit tests of the printer
#    (../check_maths.v), and texts of xtext (the standard library, the
#    thesis, real numbers) and of cyp (square_pos): every formula is
#    mathematics, none is left as code;
# 4. the formulas as code (pdf.sh --code): every formula is code;
# 5. every Typst source of 1-4 compiles to a PDF, without errors or
#    warnings (the PDFs are in tests/out/);
# 6. the HTML page of a checked text and of the unit tests (Typst's HTML
#    export): it compiles, its formulas are MathML (<math>), with the
#    classes of their roles and of the statuses;
# 7. the two syntaxes: the proposal's examples praeclarum (the paper's),
#    xtext_praeclarum and Trans_Inv, structured and free: their PDF and
#    their web page (each node an element of class p with its number, the
#    script of the hover), the same nodes in both syntaxes, the closing
#    paragraph after the sub-items, a free text as paragraphs and spans;
# 8. the round, when cyp is built (../../cyp/_build/default/bin/cyp.exe):
#    a text of xtext checked by cyp now, then its PDF; cyp's sqrt_square
#    (real numbers) checked, then its PDF and HTML page.
# 9. the links, on a small gallery (gallery.sh) of four pages: the names
#    of ABCD link to their steps (HTML anchors, PDF destinations), a
#    justification and a lemma link to their documentation, each page
#    links to the index, to the same text in French and checked by cyp,
#    and back; the legend.
#
# Needs: the opam switch elpi5, typst, qpdf; xtext built (cd xtext && make).
# typst (a snap) reads and writes only under the home directory, not /tmp.
set -e
here=$(cd "$(dirname "$0")" && pwd)
prooftext=$(dirname "$here")
repo=$(dirname "$prooftext")
out=$here/tests/out
rm -rf "$out"; mkdir -p "$out"
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)" || true
ulimit -v 8000000
xtext_flags="-R $repo/xtext XText"

# [typst_of MD [OPTION]]: the Typst source of the proof text MD next to it
# (pdf.sh --source), with xtext's load path; pdf.sh says how many formulas
# are shown as code
typst_of() {
  # $2 is an option of pdf.sh or nothing: split on purpose
  # shellcheck disable=SC2086
  sh "$prooftext/pdf.sh" --source --flags "$xtext_flags" $2 "$1" > "$out/typst_of.log" 2>&1 \
    || { cat "$out/typst_of.log"; exit 1; }
}

# [same NAME GOT WANTED]: the files GOT and WANTED are the same
same() {
  if cmp -s "$2" "$3"; then echo "ok   $1"
  else echo "FAIL $1: $2 differs from $3"; diff "$3" "$2" | head -20; exit 1; fi
}

# [formula_counts]: the number of formulas of the last text, and of those
# shown as code, from pdf.sh's report
formula_count() { sed -n 's/.*(\([0-9]*\) formulas.*/\1/p' "$out/typst_of.log"; }
code_count() { sed -n 's/.* \([0-9]*\) shown as code).*/\1/p' "$out/typst_of.log"; }

# [compile TYP]: the PDF of TYP, in the directory of TYP; typst's warnings
# are failures too
compile() {
  nice typst compile --package-path "$here" "$1" "${1%.typ}.pdf" > "$out/typst.log" 2>&1 \
    || { cat "$out/typst.log"; exit 1; }
  if [ -s "$out/typst.log" ]; then cat "$out/typst.log"; exit 1; fi
  echo "ok   PDF ${1#$out/}"
}

# [html TYP CLASS...]: the HTML page of TYP, with MathML and elements of
# each class CLASS; typst's warnings, but the one on its experimental HTML
# export, are failures
html() {
  typ=$1; shift
  nice typst compile --features html --format html --package-path "$here" "$typ" "${typ%.typ}.html" \
    > "$out/typst.log" 2>&1 || { cat "$out/typst.log"; exit 1; }
  if grep "^warning" "$out/typst.log" | grep -qv "html export is under active development"; then
    cat "$out/typst.log"; exit 1
  fi
  grep -q "<math" "${typ%.typ}.html" || { echo "FAIL HTML ${typ#$out/}: no MathML"; exit 1; }
  for class in "$@"; do
    grep -q "class=\"$class\"" "${typ%.typ}.html" \
      || { echo "FAIL HTML ${typ#$out/}: no class $class"; exit 1; }
  done
  echo "ok   HTML ${typ#$out/}"
}

echo "1. xtext's Typst = the Typst of xtext's Markdown, read back"
for typ in $(cd "$repo/xtext/examples-typst" && find . -name '*.typ' | sort); do
  name=${typ#./}; name=${name%.typ}
  mkdir -p "$out/$(dirname "$name")"
  cp "$repo/xtext/examples/$name.md" "$out/$name.md"
  typst_of "$out/$name.md"
  same "$name" "$out/$name.typ" "$repo/xtext/examples-typst/$name.typ"
done

echo "2. texts checked by cyp: the expected Typst"
for name in add_0_r half_le; do
  sed -e '/^flags: /d' "$repo/xtext/cyp-check/$name.checked.md" > "$out/$name.checked.md"
  typst_of "$out/$name.checked.md"
  same "$name.checked" "$out/$name.checked.typ" "$here/tests/$name.checked.typ"
done

echo "3. formulas as mathematics"
(cd "$out" && nice rocq c -Q "$repo/lexicon" Lexicon -Q "$prooftext" ProofText \
   "$prooftext/check_maths.v" > check_maths.log 2>&1) || { cat "$out/check_maths.log"; exit 1; }
echo "ok   unit tests of the printer ($(grep -c '^ok' "$out/check_maths.log") formulas)"
mkdir -p "$out/maths"
for md in xtext/examples/std_app_assoc.md xtext/examples/std_negb_andb.md \
          xtext/examples/std_Nat_le_trans.md xtext/examples/Tauto.md \
          xtext/examples/Trans_Inv.md xtext/examples/drinker.md \
          xtext/examples/even_or_odd.md xtext/examples/reals_sqrt_sq.md \
          xtext/examples/reals_exp_div.md cyp/examples/square_pos.md; do
  cp "$repo/$md" "$out/maths/"
  typst_of "$out/maths/$(basename "$md")"
  [ "$(code_count)" = 0 ] || { echo "FAIL $md: formulas shown as code"; cat "$out/typst_of.log"; exit 1; }
  echo "ok   $(basename "$md" .md): $(formula_count) formulas in mathematics"
done

echo "4. formulas as code"
mkdir -p "$out/code"
cp "$repo/xtext/examples/drinker.md" "$out/code/"
typst_of "$out/code/drinker.md" --code
[ "$(code_count)" = "$(formula_count)" ] || { echo "FAIL --code: formulas in mathematics"; exit 1; }
echo "ok   drinker: $(formula_count) formulas as code"

echo "5. the PDFs"
for typ in $(find "$out" -name '*.typ' | sort); do compile "$typ"; done

echo "6. the HTML pages"
html "$out/half_le.checked.typ" "formula claim" "formula hyp" "formula var" \
  "mark ok" "mark ko" "message ko" "number"
html "$out/check_maths.typ"

echo "7. the two syntaxes (the proposal's examples, structured and free)"
mkdir -p "$out/syntaxes"
for name in praeclarum xtext_praeclarum Trans_Inv; do
  for syntax in structured free; do
    cp "$repo/proposal/examples/$name.$syntax.md" "$out/syntaxes/"
    typst_of "$out/syntaxes/$name.$syntax.md"
    compile "$out/syntaxes/$name.$syntax.typ"
    # each node is an element of class p with its number, and the page
    # has the script of the hover
    html "$out/syntaxes/$name.$syntax.typ" "p" "formula claim"
    grep -q "<script>" "$out/syntaxes/$name.$syntax.html" \
      || { echo "FAIL $name.$syntax: no script for the hover"; exit 1; }
    grep -o 'data-id="[0-9.]*"' "$out/syntaxes/$name.$syntax.html" | sort > "$out/syntaxes/$name.$syntax.ids"
  done
  same "$name: the same nodes in both syntaxes" "$out/syntaxes/$name.free.ids" "$out/syntaxes/$name.structured.ids"
done
# the closing paragraph of an item comes after its sub-items, as written
typ=$out/syntaxes/praeclarum.structured.typ
[ "$(grep -n 'Altogether' "$typ" | cut -d: -f1)" -gt "$(grep -n 'step("1.2"' "$typ" | cut -d: -f1)" ] \
  || { echo "FAIL praeclarum: the closing paragraph before the sub-items"; exit 1; }
echo "ok   the closing paragraph after the sub-items"
# a free text has no list in the PDF: its nodes are spans (node), its
# text is in paragraphs
typ=$out/syntaxes/praeclarum.free.typ
grep -q '#node("1.1")' "$typ" && ! grep -q 'steps((' "$typ" \
  || { echo "FAIL praeclarum.free: not written as paragraphs and spans"; exit 1; }
echo "ok   a free text is paragraphs with spans"

echo "8. the round: xtext's text, checked by cyp, then its PDF"
cyp=$repo/cyp/_build/default/bin/cyp.exe
if [ -x "$cyp" ] && [ -f "$repo/cyp/vernac/Cyp.vo" ]; then
  mkdir -p "$out/round"
  # the flags line lets the require line of the text find xtext's files
  sed -e "s|^by: |flags: $xtext_flags\nby: |" "$repo/xtext/examples/or_commut.md" > "$out/round/or_commut.md"
  (cd "$out/round" && CYP_LIB=$repo/cyp/vernac nice "$cyp" or_commut.md)
  sh "$prooftext/pdf.sh" --source "$out/round/or_commut.checked.md" > "$out/typst_of.log" 2>&1 \
    || { cat "$out/typst_of.log"; exit 1; }
  grep -q 'numbers: true' "$out/round/or_commut.checked.typ" \
    || { echo "FAIL round: no statuses in the Typst of the checked text"; exit 1; }
  compile "$out/round/or_commut.checked.typ"
  # cyp's text on real numbers (square roots, powers, fractions), checked,
  # then its PDF and its HTML page, in mathematics
  cp "$repo/cyp/examples/sqrt_square.md" "$out/round/"
  (cd "$out/round" && CYP_LIB=$repo/cyp/vernac nice "$cyp" sqrt_square.md)
  typst_of "$out/round/sqrt_square.checked.md"
  [ "$(code_count)" = 0 ] || { echo "FAIL sqrt_square: formulas shown as code"; exit 1; }
  compile "$out/round/sqrt_square.checked.typ"
  html "$out/round/sqrt_square.checked.typ" "formula just" "mark ok"
else
  echo "skipped: cyp is not built (cd cyp && dune build ./bin/cyp.exe; cd vernac && rocq c ... Cyp.v)"
fi

echo "9. the links: a small gallery (gallery.sh), in tests/out/gallery"
gallery=$out/gallery
sh "$prooftext/gallery.sh" "$gallery" \
  "xtext:English:$xtext_flags:$repo/xtext/examples/ABCD.md $repo/xtext/examples/or_commut.md" \
  "xtext-languages:Languages:$xtext_flags:$repo/xtext/examples/fr/or_commut.md" \
  "xtext-checked:Checked:$xtext_flags:$repo/xtext/cyp-check/or_commut.checked.md" > "$out/gallery.log" 2>&1 \
  || { cat "$out/gallery.log"; exit 1; }
[ -s "$gallery/failures.txt" ] && { echo "FAIL gallery:"; cat "$gallery/failures.txt"; exit 1; }
# [has FILE TEXT WHAT]: FILE has the text TEXT
has() { grep -qF "$2" "$1" || { echo "FAIL $3: no $2 in ${1#$out/}"; exit 1; }; echo "ok   $3"; }
# the names of ABCD (h1 ... h4, given in its statement) link to it: each
# link #loc-N of the page has its anchor id="loc-N"
page=$gallery/xtext/ABCD.html
has "$page" 'href="#loc-' "names linked to their steps (HTML)"
for target in $(grep -o 'href="#loc-[0-9]*"' "$page" | sed 's/href="#\(.*\)"/\1/' | sort -u); do
  grep -q "id=\"$target\"" "$page" || { echo "FAIL HTML ABCD: no anchor $target"; exit 1; }
done
echo "ok   every link to a name has its anchor (HTML)"
qpdf --qdf --object-streams=disable "$gallery/xtext/ABCD.pdf" "$out/ABCD.qdf.pdf"
has "$out/ABCD.qdf.pdf" "/Dest" "names linked to their steps (PDF)"
# a justification and a lemma of the corelib, linked to their documentation
has "$gallery/xtext/or_commut.typ" '#just("or_intror", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_intror")' \
  "justification linked to its documentation"
has "$gallery/xtext/or_commut.html" 'href="https://rocq-prover.org/corelib/Corelib.Init.Logic.html#or_ind"' \
  "lemma in the text linked to its documentation (HTML)"
# the links between the pages: index, other languages, checked by cyp, and back
has "$gallery/xtext/or_commut.html" '<a href="../index.html">index</a>' "page to the index"
has "$gallery/xtext/or_commut.html" '<a href="../xtext-languages/fr/or_commut.html">fr</a>' "page to its other languages"
has "$gallery/xtext-languages/fr/or_commut.html" '<a href="../../xtext/or_commut.html">en</a>' "and back"
has "$gallery/xtext/or_commut.html" '<a href="../xtext-checked/or_commut.checked.html">checked by cyp</a>' "page to its checked text"
has "$gallery/xtext-checked/or_commut.checked.html" '<a href="../xtext/or_commut.html">not checked</a>' "and back"
qpdf --qdf --object-streams=disable "$gallery/xtext/or_commut.pdf" "$out/or_commut.qdf.pdf"
has "$out/or_commut.qdf.pdf" "/URI (../xtext-checked/or_commut.checked.pdf)" "PDF to the checked PDF"
has "$gallery/xtext/or_commut.html" '<footer class="legend">' "legend (HTML)"
echo "all ok"
