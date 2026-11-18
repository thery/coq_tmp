#!/bin/sh
# The PDF of proof texts: pdf.sh proof.md ... (or proof.typ ...)
#
# For each text proof.md (written by xtext, or checked by cyp:
# proof.checked.md), writes its Typst source proof.typ next to it (the
# command Typst of Typst.v, prooftext's reader and write-typst), then
# proof.pdf with typst and the template typst/local/prooftext/0.1.0 (the
# Typst package @local/prooftext).  A file .typ (Explain foo to "foo.typ")
# is compiled as it is.  Stops at the first error.
#
# Needs: the opam switch elpi5 (rocq-elpi), typst (0.15).  Typst.vo is
# compiled when it is older than its sources.
set -e
here=$(cd "$(dirname "$0")" && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)" || true
ulimit -v 8000000

# Typst.vo, compiled again when a source is newer
if [ ! -f "$here/Typst.vo" ] || [ -n "$(find "$here/Typst.v" "$here"/*.elpi "$here/../lexicon/lexicon.elpi" -newer "$here/Typst.vo")" ]; then
  (cd "$here" && nice rocq c -Q ../lexicon Lexicon -Q . ProofText Typst.v)
fi

# [typst_source MD TYP]: the Typst source of the proof text MD in TYP
typst_source() {
  tmp=$(mktemp -d)
  printf 'From ProofText Require Import Typst.\nTypst "%s" to "%s".\n' "$1" "$2" > "$tmp/typst_of.v"
  nice rocq c -Q "$here/../lexicon" Lexicon -Q "$here" ProofText "$tmp/typst_of.v" > "$tmp/out" 2>&1 \
    || { cat "$tmp/out"; rm -rf "$tmp"; exit 1; }
  rm -rf "$tmp"
}

for f in "$@"; do
  file=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  case "$file" in
    *.typ) typ=$file ;;
    *.md) typ=${file%.md}.typ; typst_source "$file" "$typ" ;;
    *) echo "pdf.sh: $f is neither .md nor .typ" >&2; exit 2 ;;
  esac
  nice typst compile --package-path "$here/typst" "$typ" "${typ%.typ}.pdf"
  echo "pdf.sh: written ${typ%.typ}.pdf"
done
