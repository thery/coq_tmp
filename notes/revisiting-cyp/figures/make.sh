#!/bin/sh
# Remakes the figures of the note from the tools of the repository that
# holds this directory (main, merged into the note's branch).
# Needs: the opam switch elpi5; cyp built (cyp/_build, cyp/vernac/Cyp.vo),
# xtext/ExtractText.vo, prooftext/pdf.sh, typst 0.15, pdftoppm,
# google-chrome (headless, for the web page).  Run from this directory.
set -e
R=$(cd ../../.. && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5)"
# at most 8 GB of memory for each run of Rocq (pdf.sh sets its own); not for
# Chrome, which reserves more address space than that
lim() { (ulimit -v 8000000; "$@"); }
export CYP_LIB=$R/cyp/vernac
CYP=$R/cyp/_build/default/bin/cyp.exe
PDF=$R/prooftext/pdf.sh
LIBS="-R $R/xtext XText -Q $R/lexicon Lexicon -Q $R/prooftext ProofText"

# the 2003 file and interface (paper of UITP 2003, page 12)
cp ~/papers/uitp/cyp/examples/praeclarum.cyp praeclarum.2003.xml
pdftoppm -f 12 -l 12 -r 250 -x 560 -y 272 -W 990 -H 536 -png -singlefile ~/papers/uitp/paper.pdf cyp2003

# praeclarum in the format of proof texts, structured and free (the
# examples of proposal/), its conditions, checked by cyp
cp "$R/proposal/examples/praeclarum.structured.md" praeclarum_tree.md
cp "$R/proposal/examples/praeclarum.free.md" praeclarum_free.md
lim "$CYP" --conditions praeclarum_tree.md > praeclarum.conditions.txt
lim "$CYP" praeclarum_tree.md
lim "$CYP" praeclarum_free.md

# xtext: plain and tagged texts, Arabic, a proof in progress, the drinker
lim rocq c -Q . Fig $LIBS xtexts.v > xtexts.out
sed -i '/^require:/a flags: -Q . Fig -R ../../../xtext XText -Q ../../../lexicon Lexicon -Q ../../../prooftext ProofText' drinker.md
lim "$CYP" drinker.md
# xtext's praeclarum checked by cyp (a copy with the load paths)
sed '/^require:/a flags: -Q . Fig -R ../../../xtext XText -Q ../../../lexicon Lexicon -Q ../../../prooftext ProofText' praeclarum_xtext.md > praeclarum_xtext_in.md
lim "$CYP" praeclarum_xtext_in.md
mv praeclarum_xtext_in.checked.md praeclarum_xtext.checked.md; rm -f praeclarum_xtext_in.md
cp "$R/cyp/examples/sqrt_square.md" sqrt_square.md
lim "$CYP" sqrt_square.md

# PDFs and the web page
"$PDF" praeclarum_tree.checked.md praeclarum_free.md sqrt_square.checked.md
"$PDF" --flags "-Q $PWD Fig $LIBS" praeclarum_xtext.md praeclarum_ar.md drinker.checked.md
"$PDF" --html praeclarum_free.md
# the hover fixed on node 1.1 by the address (headless Chrome cannot hover)
google-chrome --headless --disable-gpu --hide-scrollbars --force-device-scale-factor=2 \
  --window-size=800,265 --screenshot="$PWD/fig-hover.png" \
  "file://$PWD/praeclarum_free.html#hover=1.1" 2>/dev/null

pdftoppm -r 220 -x 130 -y 330 -W 1560 -H 470 -png -singlefile praeclarum_tree.checked.pdf fig-tree-checked
pdftoppm -r 220 -x 130 -y 330 -W 1560 -H 280 -png -singlefile praeclarum_free.pdf fig-free
pdftoppm -r 220 -x 130 -y 360 -W 1560 -H 480 -png -singlefile praeclarum_xtext.pdf fig-xtext
pdftoppm -r 220 -x 130 -y 380 -W 1560 -H 580 -png -singlefile praeclarum_ar.pdf fig-praeclarum-ar
pdftoppm -r 220 -x 130 -y 380 -W 1560 -H 440 -png -singlefile sqrt_square.checked.pdf fig-sqrt-square
pdftoppm -r 220 -x 130 -y 360 -W 1560 -H 1300 -png -singlefile drinker.checked.pdf fig-drinker-checked

rm -f ./*.typ ./*.cyp.json ./*.html ./*.vo ./*.vok ./*.vos ./*.glob ./.*.aux
