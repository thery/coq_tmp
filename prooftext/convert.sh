#!/bin/sh
# convert.sh: a proof text written again in the other style, by the Rocq
# command Convert (Convert.v, convert.elpi).
#   usage: sh convert.sh IN.md OUT.md free|structured
# free: prose, a node a span [ ... ]{.p} or a div ::: p ... :::;
# structured: one list item per node.  The rules: README.md, "Converting
# between the two styles".  Convert.vo is compiled when older than its
# sources.  Needs the switch elpi5 (Rocq, rocq-elpi).
[ $# = 3 ] && { [ "$3" = free ] || [ "$3" = structured ]; } ||
  { echo "usage: sh convert.sh IN.md OUT.md free|structured"; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)"
ulimit -v 8000000
abs() { case $1 in /*) echo "$1" ;; *) echo "$PWD/$1" ;; esac; }
in=$(abs "$1"); out=$(abs "$2")
[ -f "$in" ] || { echo "convert.sh: no file $1"; exit 2; }
Q="-Q $here/../lexicon Lexicon -Q $here ProofText"
if [ ! -f "$here/Convert.vo" ] || [ -n "$(find "$here/Convert.v" "$here"/*.elpi "$here/../lexicon/lexicon.elpi" -newer "$here/Convert.vo")" ]; then
  (cd "$here" && rocq c $Q Convert.v) || exit 1
fi
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
printf 'From ProofText Require Import Convert.\nConvert "%s" to "%s" as %s.\n' "$in" "$out" "$3" > "$tmp/convert.v"
(cd "$tmp" && rocq c $Q convert.v)
