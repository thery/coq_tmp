#!/bin/sh
# A gallery of proof texts: a web page (Typst's HTML export, the formulas
# as MathML) and a PDF per text, and an index.html that lists them.
#   usage: sh prooftext/gallery.sh OUT [SECTION:TITLE:FLAGS:FILES ...]
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
# that the repository is not written.  A text that fails is listed in
# OUT/failures.txt and left out of the index.
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
: > "$out/failures.txt"
sections=""
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
    if nice sh "$here/pdf.sh" --html --flags "$flags" "$out/$name/$sub$base.md" > /dev/null 2>&1 &&
       nice sh "$here/pdf.sh" --flags "$flags" "$out/$name/$sub$base.md" > /dev/null 2>&1; then
      echo "$sub$base" >> "$out/$name/.list"
    else
      echo "$name/$sub$base" >> "$out/failures.txt"
    fi
  done
  sections="$sections$name:$title
"
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
