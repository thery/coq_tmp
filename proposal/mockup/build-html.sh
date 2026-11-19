#!/bin/sh
# Builds mockup/{structured,free}.html from their shorthand sources.
# The colour of a justification: the template's, when it has a role
# "by" or "justification", else the placeholder of lib.typ.
cd "$(dirname "$0")"
T=../../prooftext/typst/local/prooftext/0.1.0/prooftext.typ
C=$(grep -E '^\s*(by|justification)\s*:\s*rgb\("#[0-9a-fA-F]{6}"\)' $T | head -1 | sed 's/.*"\(#[0-9a-fA-F]*\)".*/\1/')
[ -n "$C" ] || C="#cdeee3"
for f in structured free; do
  { sed "s/TITLE/Proof format: $f syntax/; s/BYCOLOUR/$C/" common-head.html
    sed -f expand.sed $f.src.html
    cat common-tail.html; } > $f.html
done
echo "justification colour: $C"
