#!/bin/sh
# Installs the tutorial's examples in rocq-web (Rocq in the browser,
# https://thery.github.io/rocq-web/) as the example "cyp-tutorial".
#   usage: sh rocq-web.sh EXAMPLES
# EXAMPLES is the examples directory of a rocq-web checkout
# (app/public/examples).  Copies the chapter files chNN_*.v and the texts
# chNN_*.md (not the checked texts) to EXAMPLES/cyp-tutorial, and adds
# the entry of the example to EXAMPLES/index.json, after the entry "cyp",
# unless an entry "cyp-tutorial" is there already.  The chapter files
# name their texts "cyp-tutorial/chNN_*.md": rocq-web runs Rocq from the
# root of the files.  The page opens a file with
# ?example=cyp-tutorial&file=ch01_first.v.
here=$(cd "$(dirname "$0")" && pwd)
ex=$1
[ -n "$ex" ] && [ -f "$ex/index.json" ] ||
  { echo "usage: sh rocq-web.sh EXAMPLES (a directory with index.json)" >&2; exit 2; }
dest=$ex/cyp-tutorial
rm -rf "$dest"; mkdir -p "$dest"
files=""
# per example NN: its .v files, then its texts .md
for nn in $(ls "$here"/ch*.v | sed "s|.*/ch\([0-9]*\)_.*|\1|" | sort -u); do
  for f in "$here"/ch${nn}_*.v "$here"/ch${nn}_*.md; do
    [ -f "$f" ] || continue
    case $f in *.checked.md) continue ;; esac
    cp "$f" "$dest/"; files="$files, \"$(basename "$f")\""
  done
done
files=${files#, }
entry="  {\"id\": \"cyp-tutorial\", \"title\": \"cyp tutorial\", \"description\": \"The examples of the cyp tutorial (cyp/TUTORIAL.md): proofs written as text, each formula tagged with its role, checked step by step by Rocq; one file per example, from a first proof to the Proof block (github.com/thery/coq_tmp).\", \"files\": [$files]},"
if grep -q '"id": "cyp-tutorial"' "$ex/index.json"; then
  echo "rocq-web.sh: index.json has an entry cyp-tutorial already: not changed"
else
  awk -v e="$entry" '{ print } /"id": "cyp",/ && !done { print e; done = 1 }' \
    "$ex/index.json" > "$ex/index.json.new" && mv "$ex/index.json.new" "$ex/index.json"
  grep -q '"id": "cyp-tutorial"' "$ex/index.json" ||
    { echo "rocq-web.sh: no entry cyp in index.json; add this line by hand:"; echo "$entry"; }
fi
echo "rocq-web.sh: $(ls "$dest" | wc -l) files in $dest"
