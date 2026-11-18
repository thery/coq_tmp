#!/bin/sh
# Optional, with cyp's reader (cyp/vernac/elpi/text.elpi): how the formulas
# of the texts are read, with and without their tags (RolesCheck.v): for
# each text, its number of lines and of lines where a formula has its role
# only by its tag.
#   usage: sh cyp-check/roles_check.sh file.md ...   (paths from xtext/)
here=$(cd "$(dirname "$0")" && pwd)
top=$(cd "$here/../.." && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi4 2>/dev/null)"
flags="-Q $top/lexicon Lexicon -Q $top/cyp/vernac CypV -Q $here XTextCheck"
(cd "$here" && rocq c $flags RolesCheck.v) || exit 1
cd "$here/.." || exit 1
[ $# -eq 0 ] && set -- examples/*.md
tmp=$(mktemp -d)
{ echo "From XTextCheck Require Import RolesCheck."
  for f in "$@"; do echo "XText_roles \"$PWD/$f\"."; done; } > "$tmp/roles_tmp.v"
rocq c $flags "$tmp/roles_tmp.v" 2>&1
rm -rf "$tmp"
