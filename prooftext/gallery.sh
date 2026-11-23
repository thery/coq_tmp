#!/bin/sh
# A gallery of proof texts: a web page (Typst's HTML export, the formulas
# as MathML) and a PDF per text, and an index.html that lists them.
#   usage: sh prooftext/gallery.sh [OPTIONS] OUT [SECTION:TITLE:FLAGS:FILES ...]
# With no section, the public gallery of the repository:
#   - xtext's texts (xtext/examples/*.md), written from Rocq proofs;
#   - the same in the other languages of the lexicon (xtext/examples/LANG/);
#   - xtext's texts checked by cyp, in English and in the other languages
#     (xtext/cyp-check/*.checked.md and xtext/cyp-check/LANG/*.checked.md);
#   - cyp's own examples, checked (cyp/examples/*.checked.md: run cyp on
#     them first).
# A section is one argument "name:Title:rocq flags:files" (the files a
# shell pattern); OUT must be under the home directory (typst is a snap).
# Each text is copied to OUT/name/ and made there (prooftext/pdf.sh), so
# that the repository is not written.  Each page links to the index, to
# the same text in the other languages and to the same text checked by
# cyp (or not checked), when the gallery has them: the same file name,
# without .checked, in any section (the language is the lang field).
# A text that fails is listed in OUT/failures.txt and left out of the
# index.
# Options, before OUT (passed to pdf.sh for every text):
#   --doc-root PREFIX=URL   the names of the libraries under PREFIX link to
#                           their rocqdoc pages under URL (pdf.sh --doc-root);
#   --name-links FILE       a table "NAME URL" per line, the addresses of the
#                           justifications that Rocq does not locate: rules,
#                           tactics (pdf.sh --name-links);
#   --source-root ROOT=URL  the justification words declared by
#                           CypJustification link to their declarations
#                           under URL (pdf.sh --source-root; the JSON that
#                           cyp wrote next to a checked text is copied with
#                           it).
# A relative URL in any of them is relative to OUT: it is written relative to
# each page (../ for each level of the page under OUT).
doc_roots=""; name_links=""; source_roots=""
while [ $# -gt 0 ]; do
  case "$1" in
    --doc-root) doc_roots="$doc_roots
$2"; shift 2 ;;
    --name-links) name_links=$(cd "$(dirname "$2")" && pwd)/$(basename "$2"); shift 2 ;;
    --source-root) source_roots="$source_roots
$2"; shift 2 ;;
    *) break ;;
  esac
done
out=$1; shift
here=$(cd "$(dirname "$0")" && pwd)
repo=$(dirname "$here")
mkdir -p "$out" || exit 1
out=$(cd "$out" && pwd)
xtext_flags="-R $repo/xtext XText"
if [ $# -eq 0 ]; then
  set -- \
    "xtext:Texts written by xtext from Rocq proofs:$xtext_flags:$repo/xtext/examples/*.md" \
    "xtext-languages:The same texts in other languages:$xtext_flags:$repo/xtext/examples/*/*.md" \
    "xtext-checked:xtext's texts checked by cyp:$xtext_flags:$repo/xtext/cyp-check/*.checked.md $repo/xtext/cyp-check/*/*.checked.md" \
    "cyp:cyp's examples, checked:-Q $repo/cyp/examples CypExamples:$repo/cyp/examples/*.checked.md"
fi
# [relative_url UP URL]: URL seen from a page UP below OUT (UP: ../../),
# when it is relative (no scheme, not absolute, not an anchor)
relative_url() {
  case $2 in *://*|/*|\#*) echo "$2" ;; *) echo "$1$2" ;; esac
}

# [link_options DIR]: the options of pdf.sh for the links of the pages in
# OUT/DIR/ (DIR ends with /): --doc-root, --source-root and --name-links, their relative
# addresses written from there (the table in OUT/DIR/.name-links).  The
# addresses have no spaces
link_options() {
  up=$(echo "$1" | sed 's|[^/]*/|../|g')
  printf '%s\n' "$doc_roots" | while read -r r; do
    [ -n "$r" ] && printf ' --doc-root %s=%s' "${r%%=*}" "$(relative_url "$up" "${r#*=}")"
  done
  printf '%s\n' "$source_roots" | while read -r r; do
    [ -n "$r" ] && printf ' --source-root %s=%s' "${r%%=*}" "$(relative_url "$up" "${r#*=}")"
  done
  if [ -n "$name_links" ]; then
    while read -r n u; do
      [ -n "$n" ] && echo "$n $(relative_url "$up" "$u")"
    done < "$name_links" > "$out/$1.name-links"
    printf ' --name-links %s' "$out/$1.name-links"
  fi
}

: > "$out/failures.txt"
: > "$out/.catalog"
sections=""
# 1. the Typst source of each text (prooftext/pdf.sh --source: the
#    formulas elaborated in Rocq), and the catalog of the texts made,
#    one line each: page|text|lang|checked (page: its path in OUT
#    without extension; text: its name without .checked, which names
#    the same text in every language and before and after cyp)
for section in "$@"; do
  name=${section%%:*}; rest=${section#*:}
  title=${rest%%:*}; rest=${rest#*:}
  flags=${rest%%:*}; files=${rest#*:}
  mkdir -p "$out/$name"
  : > "$out/$name/.list"
  for f in $files; do
    [ -f "$f" ] || continue
    # the language directory, if any, is kept in the name: fr/add_0_r
    base=$(basename "$f" .md)
    parent=$(basename "$(dirname "$f")")
    case $parent in examples|cyp-check) sub="" ;; *) sub="$parent/" ;; esac
    mkdir -p "$out/$name/$sub"
    # the copy without its flags line: the load paths of this machine, which
    # the section's flags give instead
    grep -v '^ *flags:' "$f" > "$out/$name/$sub$base.md"
    # the JSON of a checked text (cyp), for the links of its declared words
    case $f in *.checked.md) j=${f%.checked.md}.cyp.json ;; *) j=${f%.md}.cyp.json ;; esac
    [ -f "$j" ] && cp "$j" "$out/$name/$sub${base%.checked}.cyp.json"
    # the options of the links: split on purpose
    # shellcheck disable=SC2046
    if nice sh "$here/pdf.sh" --source --flags "$flags" $(link_options "$name/$sub") "$out/$name/$sub$base.md" > /dev/null 2>&1; then
      echo "$sub$base" >> "$out/$name/.list"
      lang=$(sed -n -e '1{/^ *---/!q;}' -e '2,/^ *---/{/^ *---/q;s/^ *lang: *//p;}' "$f" | head -1)
      case $base in *.checked) checked=yes ;; *) checked=no ;; esac
      echo "$name/$sub$base|${base%.checked}|${lang:-en}|$checked" >> "$out/.catalog"
    else
      echo "$name/$sub$base" >> "$out/failures.txt"
    fi
  done
  sections="$sections$name:$title
"
done

# [page_links PAGE]: the links of the page PAGE (a path of the catalog), a
# JSON list of [text, target] pairs, each target relative to the page:
# the index; the same text in the other languages (its language code);
# the same text checked by cyp, or not checked, in the same language
page_links() {
  awk -F'|' -v page="$1" '
    { pages[NR] = $1; texts[NR] = $2; langs[NR] = $3; checks[NR] = $4
      if ($1 == page) { me = NR } }
    END {
      up = ""; n = split(page, parts, "/"); for (i = 1; i < n; i++) up = up "../"
      out = "[[\"index\", \"" up "index.html\"]"
      # the other languages, in the order of their codes
      k = 0
      for (i = 1; i <= NR; i++)
        if (texts[i] == texts[me] && checks[i] == checks[me] && langs[i] != langs[me] && !(langs[i] in seen)) {
          seen[langs[i]] = i; codes[++k] = langs[i] }
      for (a = 1; a <= k; a++) for (b = a + 1; b <= k; b++) if (codes[b] < codes[a]) { t = codes[a]; codes[a] = codes[b]; codes[b] = t }
      for (a = 1; a <= k; a++) out = out ", [\"" codes[a] "\", \"" up pages[seen[codes[a]]] "\"]"
      # the other side of cyp
      for (i = 1; i <= NR; i++)
        if (texts[i] == texts[me] && langs[i] == langs[me] && checks[i] != checks[me]) {
          out = out ", [\"" (checks[i] == "yes" ? "checked by cyp" : "not checked") "\", \"" up pages[i] "\"]"
          break }
      print out "]"
    }' "$out/.catalog"
}

# 2. the web page and the PDF of each text, with its links
cut -d'|' -f1 "$out/.catalog" | while read -r page; do
  links=$(page_links "$page")
  if ! { nice sh "$here/pdf.sh" --html --links "$links" "$out/$page.typ" > /dev/null 2>&1 &&
         nice sh "$here/pdf.sh" --links "$links" "$out/$page.typ" > /dev/null 2>&1; }; then
    echo "$page" >> "$out/failures.txt"
    # left out of the index too
    sed -i "\|^${page#*/}\$|d" "$out/${page%%/*}/.list"
  fi
done

# the index: one section per group, one line per text (its page, its PDF,
# its Markdown)
{
  cat <<'EOF'
<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Proof texts</title>
<style>
:root { --bg: #fdfdfb; --fg: #1d1d1b; --muted: #6b6b66; --link: #1f5fa8; --rule: #e3e3dc; }
@media (prefers-color-scheme: dark) {
  :root { --bg: #17181a; --fg: #e8e8e3; --muted: #9a9a94; --link: #7fb2ee; --rule: #33343a; }
}
body { background: var(--bg); color: var(--fg); font: 16px/1.5 system-ui, sans-serif;
       max-width: 52rem; margin: 2rem auto; padding: 0 1rem; }
h1 { font-size: 1.6rem; margin-bottom: .2rem; }
h2 { font-size: 1.15rem; margin-top: 2rem; border-bottom: 1px solid var(--rule); padding-bottom: .2rem; }
p.intro, span.count { color: var(--muted); }
ul { list-style: none; padding: 0; columns: 2 18rem; }
li { padding: .1rem 0; break-inside: avoid; }
a { color: var(--link); text-decoration: none; }
a:hover { text-decoration: underline; }
a.side { color: var(--muted); font-size: .85em; margin-left: .4rem; }
</style></head><body>
<h1>Proof texts</h1>
<p class="intro">Proofs written as text: by <b>xtext</b> from Rocq proof terms (after Y. Coscoy's
thesis), and checked step by step by <b>cyp</b>.  Each text is a web page (its formulas as
mathematics) and a PDF.  Sources: <a href="https://github.com/thery/coq_tmp">thery/coq_tmp</a>.</p>
EOF
  printf '%s' "$sections" | while IFS=: read -r name title; do
    [ -n "$name" ] || continue
    n=$(wc -l < "$out/$name/.list")
    echo "<h2>$title <span class=\"count\">($n)</span></h2>"
    echo "<ul>"
    while read -r t; do
      echo "<li><a href=\"$name/$t.html\">$t</a><a class=\"side\" href=\"$name/$t.pdf\">PDF</a><a class=\"side\" href=\"$name/$t.md\">md</a></li>"
    done < "$out/$name/.list"
    echo "</ul>"
  done
  echo "</body></html>"
} > "$out/index.html"
echo "gallery.sh: $out/index.html ($(wc -l < "$out/failures.txt") failures, see failures.txt)"
