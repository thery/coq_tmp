#!/bin/sh
# Installs the tutorial in rocq-web (Rocq in the browser,
# https://thery.github.io/rocq-web/) as the example "cyp-tutorial": the one
# file tutorial.v, the whole tutorial to step through.
#   usage: sh rocq-web.sh EXAMPLES
# EXAMPLES is the examples directory of a rocq-web checkout
# (app/public/examples).  Copies tutorial.v to EXAMPLES/cyp-tutorial, and
# adds the entry of the example to EXAMPLES/index.json, after the entry
# "cyp", unless an entry "cyp-tutorial" is there already.  The page opens
# it with ?example=cyp-tutorial&file=tutorial.v.
here=$(cd "$(dirname "$0")" && pwd)
ex=$1
[ -n "$ex" ] && [ -f "$ex/index.json" ] ||
  { echo "usage: sh rocq-web.sh EXAMPLES (a directory with index.json)" >&2; exit 2; }
dest=$ex/cyp-tutorial
rm -rf "$dest"; mkdir -p "$dest"
cp "$here/tutorial.v" "$dest/"
entry='  {"id": "cyp-tutorial", "title": "cyp tutorial", "description": "The cyp tutorial in one file to step through: proofs written as text, each formula tagged with its role, checked step by step (github.com/thery/coq_tmp, cyp/TUTORIAL.md).", "files": ["tutorial.v"]},'
if grep -q '"id": "cyp-tutorial"' "$ex/index.json"; then
  echo "rocq-web.sh: index.json has an entry cyp-tutorial already: not changed"
else
  awk -v e="$entry" '{ print } /"id": "cyp",/ && !done { print e; done = 1 }' \
    "$ex/index.json" > "$ex/index.json.new" && mv "$ex/index.json.new" "$ex/index.json"
  grep -q '"id": "cyp-tutorial"' "$ex/index.json" ||
    { echo "rocq-web.sh: no entry cyp in index.json; add this line by hand:"; echo "$entry"; }
fi
echo "rocq-web.sh: $dest/tutorial.v"
