#!/bin/sh
# Remakes the figures of the note from the tools of ~/git/coq_tmp (main).
# Needs: the opam switch elpi5, cyp built (cyp/_build, cyp/vernac/Cyp.vo),
# prooftext/pdf.sh, typst 0.15, pdftoppm.  Run from this directory.
set -e
R=$HOME/git/coq_tmp
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5)"
export CYP_LIB=$R/cyp/vernac
CYP=$R/cyp/_build/default/bin/cyp.exe
PDF=$R/prooftext/pdf.sh
XT="-R $R/xtext XText"

# the 2003 file and interface (paper of UITP 2003, page 12)
cp ~/papers/uitp/cyp/examples/praeclarum.cyp praeclarum.2006.xml
pdftoppm -f 12 -l 12 -r 250 -x 560 -y 272 -W 990 -H 536 -png -singlefile ~/papers/uitp/paper.pdf cyp2003

# praeclarum in today's format, checked by cyp; its conditions
"$CYP" praeclarum_words.md
"$CYP" --conditions praeclarum.md > praeclarum.conditions.txt
"$CYP" praeclarum.md

# texts of xtext and of cyp, checked and typeset
cp "$R/xtext/examples/drinker.md" drinker.md
cp "$R/xtext/cyp-check/drinker.md" drinker_in.md
"$CYP" drinker_in.md || true          # one step not proved, as expected
mv drinker_in.checked.md drinker.checked.md; rm -f drinker_in.md drinker_in.cyp.json
cp "$R/cyp/examples/sqrt_square.md" sqrt_square.md
"$CYP" sqrt_square.md
cp "$R/xtext/examples/ar/praeclarum.md" praeclarum_ar.md
"$PDF" drinker.checked.md sqrt_square.checked.md
"$PDF" --flags "$XT" praeclarum_ar.md
rm -f ./*.typ ./*.cyp.json

pdftoppm -r 220 -x 160 -y 350 -W 1500 -H 1420 -png -singlefile drinker.checked.pdf fig-drinker-checked
pdftoppm -r 220 -x 160 -y 390 -W 1500 -H 430 -png -singlefile sqrt_square.checked.pdf fig-sqrt-square
pdftoppm -r 220 -x 160 -y 390 -W 1500 -H 600 -png -singlefile praeclarum_ar.pdf fig-praeclarum-ar

# the hand-written mock-ups of the format being implemented (branch format-v2)
M=$HOME/git/coq_tmp-formatv2/proposal/render/structured.pdf
pdftoppm -r 220 -x 160 -y 334 -W 1500 -H 322 -png -singlefile "$M" fig-mockup-praeclarum
pdftoppm -r 220 -x 160 -y 1196 -W 1500 -H 370 -png -singlefile "$M" fig-mockup-xtext
