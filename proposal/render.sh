#!/bin/sh
# Renders the mock-ups of the proposal: PDFs and PNGs in render/.
# Typst is a snap here: everything stays under the home directory.
#
# The mock-ups (mockup/lib.typ) are written over the template as it was
# when the proposal was made (commit 352fc09); the template has changed
# since (the tree, the role just), so they are compiled with that version,
# taken from git into a temporary package directory.
set -e
cd "$(dirname "$0")"
P=$(mktemp -d "$PWD/.template.XXXXXX")
trap 'rm -rf "$P"' EXIT
mkdir -p "$P/local/prooftext/0.1.0"
for f in prooftext.typ typst.toml; do
  git show "352fc09:prooftext/typst/local/prooftext/0.1.0/$f" > "$P/local/prooftext/0.1.0/$f"
done
typst compile --package-path "$P" mockup/structured.typ render/structured.pdf
typst compile --package-path "$P" --input brackets=on mockup/free.typ render/free-brackets.pdf
typst compile --package-path "$P" --input brackets=off mockup/free.typ render/free-plain.pdf
typst compile --package-path "$P" --input brackets=corners mockup/free.typ render/free-corners.pdf
for f in structured free-brackets free-plain free-corners; do
  rm -f render/$f-*.png
  pdftoppm -png -r 110 render/$f.pdf render/$f
done
sh mockup/build-html.sh
for f in structured free; do
  google-chrome --headless --disable-gpu --hide-scrollbars --window-size=900,1500 \
    --screenshot="$PWD/render/$f-html.png" "file://$PWD/mockup/$f.html" 2>/dev/null || true
done
# the hover, fixed by the address (headless Chrome cannot hover)
google-chrome --headless --disable-gpu --hide-scrollbars --window-size=900,1500 \
  --screenshot="$PWD/render/free-html-hover.png" "file://$PWD/mockup/free.html#hover=x1.1.1" 2>/dev/null || true
google-chrome --headless --disable-gpu --hide-scrollbars --window-size=900,1500 \
  --screenshot="$PWD/render/free-html-by.png" "file://$PWD/mockup/free.html#by=x1.1.1.1/i" 2>/dev/null || true
google-chrome --headless --disable-gpu --hide-scrollbars --window-size=900,1500 \
  --screenshot="$PWD/render/structured-html-hover.png" "file://$PWD/mockup/structured.html#hover=x1.1.1" 2>/dev/null || true
