#!/bin/sh
# The PDF of proof texts: pdf.sh [options] proof.md ... (or proof.typ ...)
#
# For each text proof.md (written by xtext, or checked by cyp:
# proof.checked.md), writes its Typst source proof.typ next to it (the
# command Typst of Typst.v, prooftext's reader and write-typst-in), then
# proof.pdf with typst and the template typst/local/prooftext/0.1.0 (the
# Typst package @local/prooftext).  A file .typ (ExtractText foo to "foo.typ")
# is compiled as it is.  Stops at the first error.
#
# The formulas are mathematics (maths.elpi): each is elaborated in Rocq,
# after the require line of the text's header, with the load paths of its
# flags line.  Options:
#   --code          the formulas as Rocq code (monospace), as written;
#   --maths         the formulas as mathematics (the default);
#   --flags "F"     more options of rocq c for the require line (-R, -Q);
#   --html          an HTML page proof.html in place of the PDF (Typst's
#                   HTML export, experimental: its maths are MathML);
#   --source        the Typst source only, no PDF;
#   --links JSON    links to other pages above the text, a JSON list of
#                   [text, target] pairs (gallery.sh; the template's
#                   page-links): typst compile --input links=JSON;
#   --roles R,...   colour only the formulas of these roles (var, hyp,
#                   claim, goal, fact, just), the others plain; all by
#                   default (an open goal keeps its frame).  On the web page
#                   the legend turns each role on and off.
#
# Needs: the opam switch elpi5 (rocq-elpi), typst (0.15).  Typst.vo is
# compiled when it is older than its sources.
set -e
here=$(cd "$(dirname "$0")" && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)" || true
ulimit -v 8000000

style=maths; extra_flags=""; output=pdf; links="[]"; roles=""
while [ $# -gt 0 ]; do
  case "$1" in
    --code) style=code; shift ;;
    --maths) style=maths; shift ;;
    --flags) extra_flags="$extra_flags $2"; shift 2 ;;
    --html) output=html; shift ;;
    --source) output=none; shift ;;
    --links) links=$2; shift 2 ;;
    --roles) roles=$2; shift 2
      for r in $(echo "$roles" | tr ',' ' '); do
        case $r in var|hyp|claim|goal|fact|just) ;;
          *) echo "pdf.sh: unknown role $r (var, hyp, claim, goal, fact, just)" >&2; exit 2 ;;
        esac
      done ;;
    *) break ;;
  esac
done

# Typst.vo, compiled again when a source is newer
if [ ! -f "$here/Typst.vo" ] || [ -n "$(find "$here/Typst.v" "$here"/*.elpi "$here"/../lexicon/*.elpi -newer "$here/Typst.vo")" ]; then
  (cd "$here" && nice rocq c -Q ../lexicon Lexicon -Q . ProofText Typst.v)
fi

# [header_field KEY MD]: the value of the field KEY in the header of MD
# (the lines between the first two lines ---), empty if there is none
header_field() {
  sed -n -e '1{/^ *---/!q;}' -e '2,/^ *---/{/^ *---/q;p;}' "$2" \
    | sed -n "s/^ *$1: *//p" | head -1
}

# [typst_source MD TYP]: the Typst source of the proof text MD in TYP; for
# mathematics, the require line of MD is run first, with its flags
typst_source() {
  tmp=$(mktemp -d)
  if [ "$style" = maths ]; then
    require=$(header_field require "$1"); flags="$(header_field flags "$1") $extra_flags"
    option=""
  else
    require=""; flags=""; option=" as code"
  fi
  printf '%s\nFrom ProofText Require Import Typst.\nTypst "%s" to "%s"%s.\n' \
    "$require" "$1" "$2" "$option" > "$tmp/typst_of.v"
  # $flags is a list of options: split on purpose
  # shellcheck disable=SC2086
  nice rocq c -Q "$here/../lexicon" Lexicon -Q "$here" ProofText $flags "$tmp/typst_of.v" > "$tmp/out" 2>&1 \
    || { cat "$tmp/out"; rm -rf "$tmp"; exit 1; }
  grep "^Typst: written" "$tmp/out" || true
  rm -rf "$tmp"
}

for f in "$@"; do
  file=$(cd "$(dirname "$f")" && pwd)/$(basename "$f")
  case "$file" in
    *.typ) typ=$file ;;
    *.md) typ=${file%.md}.typ; typst_source "$file" "$typ" ;;
    *) echo "pdf.sh: $f is neither .md nor .typ" >&2; exit 2 ;;
  esac
  case $output in
    pdf) nice typst compile --input "links=$links" --input "roles=$roles" --package-path "$here/typst" "$typ" "${typ%.typ}.pdf"
         echo "pdf.sh: written ${typ%.typ}.pdf" ;;
    html) # typst warns that its HTML export is experimental: that warning
          # is left out, the others are shown
          log=$(nice typst compile --features html --format html --input "links=$links" --input "roles=$roles" --package-path "$here/typst" \
            "$typ" "${typ%.typ}.html" 2>&1) || { echo "$log"; exit 1; }
          echo "$log" | grep -v "^warning: html export\|^ *= hint\|^$" || true
          echo "pdf.sh: written ${typ%.typ}.html" ;;
  esac
done
