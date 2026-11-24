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
#   --doc-root P=U  the names of the libraries whose logical path starts
#                   with P (a first component: ProofText) link to their entries
#                   in the rocqdoc pages under U (U/P.File.html#name, the
#                   scheme of rocq doc --html; U ends with /, may be
#                   relative to the page); repeatable (links.elpi,
#                   library-documentation);
#   --name-links F  the table F, one line "NAME URL" each (NAME may be
#                   several words), gives the address of a justification
#                   *NAME*{.just} that Rocq does not locate: a rule, a
#                   tactic (links.elpi, name-url);
#   --source-root R=U  a justification word that the text uses and that a
#                   CypJustification declares (cyp/vernac/Cyp.v; cyp's
#                   JSON next to the text, proof.cyp.json, lists them with
#                   the place of their declaration) links to that place:
#                   Upath#Lline (U ends with /), for a declaration in a file under the
#                   directory R (/...), or in a library under the logical
#                   prefix R (CypV: CypV.Cyp is the file Cyp.v);
#                   repeatable; no link without it;
#
# Needs: the opam switch elpi5 (rocq-elpi), typst (0.15).  Typst.vo is
# compiled when it is older than its sources.
set -e
here=$(cd "$(dirname "$0")" && pwd)
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=elpi5 2>/dev/null)" || true
ulimit -v 8000000

# [elpi_clause PRED A B]: the Elpi clause prooftext.PRED "A" "B". (after a
# newline), its strings escaped
elpi_string() { printf '"%s"' "$(printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g')"; }
elpi_clause() { printf '\nprooftext.%s %s %s.' "$1" "$(elpi_string "$2")" "$(elpi_string "$3")"; }

# [declaration_url LIBRARY FILE LINE]: the address of a declaration of a
# justification word (CypJustification, cyp/vernac/Cyp.v) under the first
# --source-root that holds it: ROOT a directory (/...), FILE under it; or
# ROOT a logical prefix (CypV), LIBRARY under it (CypV.Cyp: the file Cyp.v);
# URL/path#Lline (the line anchors of GitHub; ignored elsewhere).  Empty
# when no root holds it
declaration_url() {
  printf '%s\n' "$source_roots" | while read -r r; do
    [ -n "$r" ] || continue
    root=${r%%=*}; url=${r#*=}
    case $root in
      /*) case $2 in "${root%/}"/*) echo "$url${2#"${root%/}"/}#L$3"; break ;; esac ;;
      *) case $1 in "$root".*) echo "$url$(echo "${1#"$root".}" | tr . /).v#L$3"; break ;; esac ;;
    esac
  done
}

# [declaration_clauses MD]: the clauses name-url of the declared words that
# the text MD uses, from the JSON that cyp wrote next to it (proof.cyp.json
# for proof.md and proof.checked.md: "justifications", one word per line),
# their addresses given by --source-root; none without a root
declaration_clauses() {
  case $1 in *.checked.md) json=${1%.checked.md}.cyp.json ;; *) json=${1%.md}.cyp.json ;; esac
  [ -n "$source_roots" ] && [ -f "$json" ] || return 0
  # one line each, its fields separated by tabs (a word may have spaces:
  # *mean value inequality*{.just}), an empty field kept by its colon
  tab=$(printf '\t')
  sed -n 's/^{"word":"\([^"]*\)","meaning":"[^"]*","library":"\([^"]*\)","file":"\([^"]*\)","line":\([0-9]*\)}.*$/\1\t:\2\t:\3\t\4/p' "$json" |
    while IFS="$tab" read -r w lib file line; do
      lib=${lib#:}; file=${file#:}
      u=$(declaration_url "$lib" "$file" "$line")
      if [ -n "$u" ]; then elpi_clause name-url "$w" "$u"; fi
    done
}

# [name_link_clauses F]: the clauses name-url of the table F, one line
# "NAME URL" each: the URL is the last field, the name the words before it
# (a name may be several words: mean value inequality URL)
name_link_clauses() {
  while read -r l; do
    case $l in
      "") ;;
      *[[:space:]]*) n=${l%[[:space:]]*}; n=${n%"${n##*[![:space:]]}"}; elpi_clause name-url "$n" "${l##*[[:space:]]}" ;;
      *) elpi_clause name-url "$l" "" ;;
    esac
  done < "$1"
}

style=maths; extra_flags=""; output=pdf; links="[]"; roles=""; clauses=""; source_roots=""
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
    --doc-root) case $2 in *=*) ;; *) echo "pdf.sh: --doc-root PREFIX=URL" >&2; exit 2 ;; esac
                clauses="$clauses$(elpi_clause library-documentation "${2%%=*}" "${2#*=}")"; shift 2 ;;
    --name-links) [ -f "$2" ] || { echo "pdf.sh: no file $2" >&2; exit 2; }
                  clauses="$clauses$(name_link_clauses "$2")"; shift 2 ;;
    --source-root) case $2 in *=*) ;; *) echo "pdf.sh: --source-root ROOT=URL" >&2; exit 2 ;; esac
                   source_roots="$source_roots
$2"; shift 2 ;;
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
  # the clauses of --doc-root and --name-links, and those of the words that
  # the text uses (--source-root), before the command runs
  all_clauses="$clauses$(declaration_clauses "$1")"
  if [ -n "$all_clauses" ]; then
    { echo "Elpi Accumulate Typst lp:{{"; printf '%s\n' "$all_clauses"; echo "}}."; } > "$tmp/clauses"
    sed -i "/^From ProofText Require Import Typst\.\$/r $tmp/clauses" "$tmp/typst_of.v"
  fi
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
