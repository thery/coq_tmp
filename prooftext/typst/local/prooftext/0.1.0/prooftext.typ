// prooftext: the look of a proof text in Typst.
//
// A proof text (../../../../README.md) written in Typst by the writer
// write-typst (prooftext/typst.elpi) is a call of the functions below:
//
//   #import "@local/prooftext:0.1.0": *
//   #show: proof-text.with(lang: "en", numbers: false)
//   #title-block("and_swap", (("require", "From Stdlib Require Import Lia."),))
//   #proof([#"Let "#var($A, B : "Prop"$)#". We prove "#claim($A ∧ B → B ∧ A$)#"."], (
//     steps((
//       step("1", [#"Assume "#hyp($A ∧ B$)#" "#name("h")#"."], (
//         steps((
//           step("1.1", [#"By "#just("h")#" we have "#claim($B ∧ A$)#"."], (), status: "ko"),
//         )),
//         message("ko", "not proved: B /\\ A"),
//       ), status: "ok"),
//     )),
//     paragraph[#"Free text, "#node("2")[#mark("ok")#"a span"]#"."],
//   ), status: "ok")
//
// Each formula is shown as mathematics (or as Rocq code, monospace, when
// it is given as a string: #claim("B /\\ A")), in the style of its role;
// the items are indented by their depth, the spans and divs of a free
// text are not shown (their text is); the status of a node (in a text
// checked by cyp) is a coloured mark in front of it.

// ------------------------------------------------------------------
// Colours and fonts

// The look of the roles of a formula.  The text of every formula is
// black, the colour of the text; its role is given by a light background,
// a tint of a colour of the Okabe-Ito palette, which stays distinct for
// colour-blind readers: variables sky blue, hypotheses orange, claims
// yellow, facts grey; the name in a justification (the paper's <j>)
// reddish purple, darker, so that it stays apart from the variables and
// the facts for red-green colour blindness.  A formula without a role
// (plain) has none.  The
// legend also shows each role's mark that needs no colour (claims a thin
// frame, hypotheses a dashed underline, facts a dotted underline); the
// formulas of the text have their background only.

// the background of the formulas of each role (none: no background)
#let role-backgrounds = (
  var: rgb("#d4ebf9"),
  hyp: rgb("#f8d49c"),
  claim: rgb("#fcf6c6"),
  fact: rgb("#e3e3e3"),
  just: rgb("#d9a9cb"),
  plain: none,
)

// [shown-roles]: the roles whose formulas are coloured, given by the
// command line (typst compile --input roles=var,claim; pdf.sh --roles):
// all of them by default.  The others look like plain formulas, and in
// the PDF the legend leaves them out; the web page lists them all in its
// legend, as switches, the given ones on
#let shown-roles = {
  let given = sys.inputs.at("roles", default: "")
  if given == "" { role-backgrounds.keys() }
  else { given.split(",").map(str.trim) + ("plain",) }
}

// the mark of each role that needs no colour: a frame or an underline
// ("solid", "dashed", "dotted"), none for none
#let role-cues = (
  var: none,
  hyp: (line: "underline", dash: "dashed"),
  claim: (line: "frame", dash: "solid"),
  fact: (line: "underline", dash: "dotted"),
  just: (line: "underline", dash: "solid"),
  plain: none,
)

// the colour of the frames and underlines of the roles
#let cue-colour = rgb("#4d4d4d")

// the colour of the links (Okabe-Ito blue): to the step that introduced
// a name, to the documentation of a lemma, between the pages of a gallery
#let link-colour = rgb("#0072b2")

// the mark and the colour of each status of a step checked by cyp: proved
// (ok), not proved (ko), left to a Proof block (todo), nothing to check
// (none)
#let status-marks = (
  ok: (mark: "✔", colour: rgb("#1d7a33")),
  ko: (mark: "✘", colour: rgb("#c62828")),
  todo: (mark: "◆", colour: rgb("#d9822b")),
  "none": (mark: "▫", colour: rgb("#9e9e9e")),
)

// the fonts of the text and of the formulas: for each character, the
// first font that has it (Latin and Cyrillic: Libertinus; Arabic: Noto
// Naskh; Chinese and Korean: Noto Serif CJK); the fonts of a language
// come before the others, after Libertinus (Korean: the Korean forms of
// the CJK font)
#let latin-font = "Libertinus Serif"
#let text-fonts = ("Noto Serif", "Noto Naskh Arabic",
  "Noto Serif CJK SC", "Noto Serif CJK KR", "DejaVu Sans")
#let code-fonts = ("DejaVu Sans Mono", "Noto Sans Mono CJK SC",
  "Noto Sans Mono CJK KR", "Noto Sans Mono")
#let language-fonts = (
  zh: ("Noto Serif CJK SC",),
  ko: ("Noto Serif CJK KR",),
)
// the font of the marks of the steps (bullets and statuses)
#let mark-font = "DejaVu Sans"

// the indentation of one level of steps
#let step-indent = 1.4em

// the languages written from right to left
#let rtl-languages = ("ar", "he", "fa", "ur")

// [pad-start(amount, body)]: body, with a space amount before it, at the
// start of the lines (at the right in a text written from right to left)
#let pad-start(amount, body) = context {
  if text.dir == rtl { pad(right: amount, body) } else { pad(left: amount, body) }
}


// ------------------------------------------------------------------
// The two targets
//
// The same Typst source gives a PDF (typst compile) and an HTML page
// (typst compile --features html --format html; Typst's maths become
// MathML).  Typst's HTML export ignores the page layout (grids, padding,
// colours of text), so each function below has an HTML version: elements
// with a class (span class="formula claim", li class="step"), and the
// look in a style sheet made from the same colours (html-style).

// [on-html(html-version, paged-version)]: the first function's content
// for an HTML page, the second's for a PDF
#let on-html(html-version, paged-version) = context {
  if target() == "html" { html-version() } else { paged-version() }
}

// [element(tag, class, body)]: an HTML element of a class
#let element(tag, class, body) = html.elem(tag, attrs: (class: class), body)

// [css-cue(cue)]: the CSS of a role's mark that needs no colour: a
// border (the box of the PDF), not a text decoration, which MathML does
// not draw
#let css-cue(cue) = {
  if cue == none { "" }
  else if cue.line == "frame" { " border: 1px " + cue.dash + " " + cue-colour.to-hex() + ";" }
  else { " border-bottom: 1px " + cue.dash + " " + cue-colour.to-hex() + ";" }
}

// [hover-script]: the script of the web page (decision 8 of the
// proposal): under the pointer, a node (an element of class p) and what
// it rests on: its conclusion framed, its hypotheses dashed, its direct
// subnodes tinted, and the formulas that its justifications, its names
// and its facts point to outlined (a link to a name leads to the place
// just after the formula that introduced it; a fact without a name is
// the last hypothesis or conclusion before it with the same text).  The
// address page.html#hover=1.2 fixes the hover on node 1.2 (for a
// screenshot: a headless browser cannot hover)
#let hover-script = "
const marks = ['cur', 'sub', 'c-cur', 'h-cur', 'ref-target'];
// the elements of a selector whose innermost node is p
function own(p, selector) {
  return [...p.querySelectorAll(selector)].filter(e => e.closest('.p') === p);
}
// the formula that a link to a name leads to
function named(a) {
  const place = document.getElementById(a.getAttribute('href').slice(1));
  if (!place) return null;
  const f = place.previousElementSibling;
  return f && f.matches('.formula') ? f : null;
}
// the last hypothesis or conclusion before the fact f with its text
function repeated(f) {
  let found = null;
  for (const g of document.querySelectorAll('.p .formula.hyp, .p .formula.claim'))
    if ((g.compareDocumentPosition(f) & Node.DOCUMENT_POSITION_FOLLOWING)
        && g.textContent === f.textContent) found = g;
  return found;
}
function show(p) {
  for (const m of marks) document.querySelectorAll('.' + m).forEach(e => e.classList.remove(m));
  if (!p) return;
  p.classList.add('cur');
  for (const q of p.querySelectorAll('.p'))
    if (q.parentElement.closest('.p') === p) q.classList.add('sub');
  own(p, '.formula.claim').forEach(c => c.classList.add('c-cur'));
  own(p, '.formula.hyp').forEach(h => h.classList.add('h-cur'));
  const targets = own(p, 'a[href^=\"#\"]').map(named)
    .concat(own(p, '.formula.fact').map(repeated));
  targets.forEach(t => { if (t) t.classList.add('ref-target'); });
}
document.addEventListener('mouseover', e => show(e.target.closest('.p')));
const fixed = location.hash.match(/^#hover=(.+)$/);
if (fixed) show(document.querySelector('.p[data-id=\"' + fixed[1] + '\"]'));
"

// the style sheet of an HTML page: the backgrounds and marks of the roles
// and the colours of the statuses (those of the PDF), the indentation of
// the items, the links, the legend, the hover
#let html-style = {
  let rules = (
    ".proof-text { font-family: 'Libertinus Serif', 'Noto Serif', serif; max-width: 48em; margin: 2em auto; padding: 0 1em; line-height: 1.6; color: #000; background: #fff; }",
    ".proof-text code { font-family: 'DejaVu Sans Mono', monospace; font-size: 0.9em; }",
    ".proof-text math { font-family: 'Latin Modern Math', 'STIX Two Math', math; }",
    ".proof-text header h1 { font-size: 1.5em; margin-bottom: 0.3em; }",
    ".proof-text table.fields { font-size: 0.8em; color: #505050; border-bottom: 1px solid #b4b4b4; padding-bottom: 0.5em; width: 100%; }",
    ".proof-text table.fields th { text-align: start; padding-inline-end: 0.8em; vertical-align: top; width: 1%; white-space: nowrap; }",
    ".proof-text a { color: " + link-colour.to-hex() + "; text-decoration: none; }",
    ".proof-text a:hover { text-decoration: underline; }",
    ".formula { border-radius: 2px; padding: 0 1px; -webkit-box-decoration-break: clone; box-decoration-break: clone; }",
    ".name { font-size: 0.9em; }",
    "ul.steps { list-style: none; padding-inline-start: " + repr(step-indent) + "; margin: 0; }",
    ".proof-text > ul.steps { padding-inline-start: 0; }",
    "li.step, p.statement { margin: 0.5em 0; }",
    ".mark { display: inline-block; width: 1.3em; font-family: 'DejaVu Sans', sans-serif; font-weight: bold; color: #6e6e6e; }",
    ".number { color: #828282; font-size: 0.75em; margin-inline-end: 0.6em; }",
    ".conditions { color: " + status-marks.todo.colour.to-hex() + "; font-size: 0.8em; }",
    ".message { margin: 0.4em 0 0 1.3em; padding: 0.35em 0.6em; font-size: 0.85em; border-inline-start: 2px solid; border-radius: 2px; }",
    "nav.gallery { font-size: 0.8em; color: #6e6e6e; margin-bottom: 1em; }",
    "nav.gallery a { margin-inline-end: 0.9em; }",
    "footer.legend { margin-top: 2em; padding-top: 0.4em; border-top: 1px solid #d0d0d0; font-size: 0.75em; color: #505050; }",
    "footer.legend span.entry { margin-inline-end: 1.2em; white-space: nowrap; }",
    ".mark.inline { width: auto; font-size: 0.8em; margin-inline-end: 0.2em; }",
    "p.para { margin: 0.5em 0; }",
    "li.step > p.para { margin: 0.3em 0; }",
    // the hover (hover-script): the node under the pointer, its direct
    // subnodes, its conclusion, its hypotheses, what its names point to
    ".p { border-radius: 3px; -webkit-box-decoration-break: clone; box-decoration-break: clone; }",
    "li.p.cur, div.p.cur:not([data-id=\"0\"]) { background: rgba(0, 0, 0, 0.03); }",
    ".p.sub { background: rgba(0, 114, 178, 0.10); }",
    ".formula.claim.c-cur { outline: 1.5px solid #333; }",
    ".formula.hyp.h-cur { outline: 1.5px dashed #333; }",
    ".ref-target { outline: 2px solid " + link-colour.to-hex() + "; }",
  )
  for (role, background) in role-backgrounds {
    rules.push(".formula." + role + " {"
      + (if background == none { "" } else { " background: " + background.to-hex() + ";" }) + " }")
    // the mark of the role, in the legend only
    let mark = css-cue(role-cues.at(role))
    if mark != "" { rules.push("footer.legend .formula." + role + " {" + mark + " }") }
    // the legend's switch of the role: unchecked, the role's formulas in
    // the text lose their background (CSS only, no script)
    rules.push("body:has(#show-" + role + ":not(:checked)) .formula." + role
      + ":not(footer.legend .formula) { background: none; }")
  }
  rules.push("footer.legend label { cursor: pointer; }")
  rules.push("footer.legend input { margin: 0 0.3em 0 0; vertical-align: middle; }")
  for (status, s) in status-marks {
    rules.push(".mark." + status + " { color: " + s.colour.to-hex() + "; }")
    rules.push(".message." + status + " { border-color: " + s.colour.to-hex()
      + "; background: " + s.colour.lighten(90%).to-hex() + "; }")
  }
  rules.join("\n")
}

// ------------------------------------------------------------------
// The parts of the text of a step

// [role-look(role, body, cue: false)]: body in the PDF with the look of
// the role: a box with its background, and with cue: true (the legend)
// its mark too (a frame, or a line under it).
// Typst's highlights and underlines do not reach the symbols of maths,
// hence a box.  A box does not break across lines: a formula wider than
// the line is a box as wide as the line, where it breaks (on its own
// lines)
#let role-look(role, body, cue: false) = {
  let background = if role in shown-roles { role-backgrounds.at(role) } else { none }
  let cue = if cue { role-cues.at(role) } else { none }
  let line = if cue == none { none } else { (paint: cue-colour, thickness: 0.5pt, dash: cue.dash) }
  let stroke = if cue == none { none } else if cue.line == "frame" { line } else { (bottom: line) }
  if background == none and stroke == none { body }
  else {
    box(layout(size => {
      if measure(body).width <= size.width {
        box(fill: background, stroke: stroke, inset: (x: 1.5pt), outset: (y: 2.5pt), radius: 1.5pt, body)
      } else {
        box(width: size.width, fill: background, stroke: stroke, inset: 3pt, radius: 1.5pt, body)
      }
    }))
  }
}

// a formula of role Role ("var", "hyp", "claim", "fact" or "plain"):
// mathematics (content, $...$, printed from its Rocq term), or its text
// in Rocq syntax (a string), shown as code
#let formula-of(role, body) = {
  let written = if type(body) == str { raw(body) } else { body }
  on-html(
    () => element("span", "formula " + role, written),
    () => role-look(role, written))
}

// a variable, a hypothesis, a claim, a fact, a formula without a role
#let var(body) = formula-of("var", body)
#let hyp(body) = formula-of("hyp", body)
#let claim(body) = formula-of("claim", body)
#let fact(body) = formula-of("fact", body)
#let formula(body) = formula-of("plain", body)

// [linked(destination, body)]: body as a link, in the colour of the
// links: destination is a label (the step that introduced a name), an
// address (the documentation of a lemma, a page) or none (no link)
#let linked(destination, body) = {
  if destination == none { body }
  else { link(destination, on-html(() => body, () => std.text(fill: link-colour, body))) }
}

// [anchor(label)]: the place a link to the label leads to (nothing for
// none).  In the HTML page, Typst writes it as an element with an id
// (loc-N), and the links to it as href="#loc-N"
#let anchor(label) = if label == none { [] } else { [#metadata(none)#std.label(label)] }

// the name given to the formula before it, (h): label, when the name is
// introduced here, the place the uses of the name lead to; target, when
// the formula is a fact that names a hypothesis, the label of the step
// that introduced it
#let name(text, label: none, target: none) = {
  anchor(label)
  let shown = linked(if target == none { none } else { std.label(target) }, raw(text))
  on-html(
    () => element("span", "name", [(#shown)]),
    () => std.text(size: 0.9em, [(#shown)]))
}

// a name used in the text ("By h4", "Applying h2 to h4"), linked to the
// node that introduced it (its label target)
#let named(text, target) = linked(std.label(target), raw(text))

// a lemma, a constructor or a type named in the text ("Applying
// f_equal_nat"), linked to its entry in the documentation of its library
#let cited(text, url) = linked(url, raw(text))

// a justification, *X*{.just}: the name X in the colour of the
// justifications (a role, "just", as a formula's), linked to the
// documentation of the lemma (url) or to the node that introduced the
// name X (target).  The words around it ("by", "applying") are plain text
#let just(text, url: none, target: none) = {
  let destination = if url != none { url } else if target != none { std.label(target) } else { none }
  formula-of("just", linked(destination, raw(text)))
}

// ------------------------------------------------------------------
// The document

// [page-links]: the links of a page of a gallery to its other pages,
// given by the command line (typst compile --input links=JSON, gallery.sh
// through pdf.sh --links): a list of (text, target) pairs, each target a
// path relative to the page.  A target without an extension leads to
// the page of the same kind, .html for the HTML page, .pdf for the PDF;
// an empty list for a text outside a gallery
#let page-links = json(bytes(sys.inputs.at("links", default: "[]")))

// [gallery-links()]: the links of page-links, in a small line above the
// text (nothing outside a gallery)
#let gallery-links() = if page-links.len() > 0 {
  let entry(extension, l) = {
    let (text, target) = l
    let path = if target.ends-with(".html") or target.ends-with(".pdf") { target } else { target + extension }
    linked(path, text)
  }
  on-html(
    () => html.elem("nav", attrs: (class: "gallery"), page-links.map(l => entry(".html", l)).join()),
    () => block(below: 1em, std.text(size: 0.8em, fill: luma(110),
      page-links.map(l => entry(".pdf", l)).join(h(0.9em)))))
}

// [proof-text(lang, numbers, body)]: the page and the fonts of the text in
// the language lang; numbers: the numbers of the steps are shown (those
// of cyp's conditions, in Dewey notation).  Above the text, the links
// of a page of a gallery (page-links)
#let show-numbers = state("prooftext-numbers", false)
#let proof-text(lang: "en", numbers: false, body) = {
  set text(lang: lang, dir: if lang in rtl-languages { rtl } else { ltr })
  show-numbers.update(numbers)
  on-html(
    () => {
      html.elem("style", html-style)
      html.elem("div", attrs: (class: "proof-text", lang: lang,
        dir: if lang in rtl-languages { "rtl" } else { "ltr" }), gallery-links() + body)
    },
    () => {
      set page(paper: "a4", margin: (x: 2cm, y: 2cm), numbering: "1")
      set text(font: (latin-font,) + language-fonts.at(lang, default: ()) + text-fonts,
        size: 10.5pt)
      // the formulas as Rocq code are written from left to right in every
      // language
      show raw: set text(font: code-fonts, size: 0.92em, dir: ltr)
      set par(justify: false, leading: 0.7em)
      gallery-links()
      body
    })
}

// [title-block(name, fields)]: the name of the theorem, and the fields of
// the header (key, value) in a small table
#let title-block(name, fields) = on-html(
  () => html.elem("header", {
    html.elem("h1", raw(name))
    if fields.len() > 0 {
      element("table", "fields",
        for (key, value) in fields { html.elem("tr", html.elem("th", key) + html.elem("td", raw(value))) })
    }
  }),
  () => block(below: 1.2em, {
    std.text(size: 1.5em, weight: "bold", raw(name))
    if fields.len() > 0 {
      v(0.4em)
      set std.text(size: 0.8em, fill: luma(80))
      grid(columns: (auto, 1fr), column-gutter: 0.8em, row-gutter: 0.45em,
        ..fields.map(((key, value)) => (strong(key), raw(value))).flatten())
    }
    v(0.3em)
    line(length: 100%, stroke: 0.5pt + luma(180))
  }))

// ------------------------------------------------------------------
// The nodes of the proof
//
// A proof text is the tree of its nodes (prooftext/README.md, "The
// format").  The writer gives the top node to proof: its first paragraph
// (the statement), then its blocks.  The blocks of a node are made by
// paragraph, steps (a list of items, each a step), division (a div,
// ::: p) and message (cyp's message about a node); they are values, which
// proof and step lay out at their depth.  A span [ ... ]{.p} is node,
// inside the text of a paragraph.
//
// The PDF shows the items as a list (a bullet or a status mark, the
// sub-items one level further in, the paragraphs after the sub-items at
// the level of the item's text), and the spans and the divs not at all:
// their text is that of the paragraphs the author wrote, with only the
// status mark of a checked node at its start.  The web page has the same
// look, and each node, whatever its syntax, is an element of class p with
// its number (data-id), for the hover (hover-script).

// The status of a node is that of a text checked by cyp, with cyp's names
// (its .cyp.json): "ok", "ko", "todo", "none" (nothing to check in the
// node); a text that is not checked has none (the value), and its items a
// bullet.

// the mark in front of a node of status status, a bullet for an item that
// is not checked (and nothing for a statement that is not checked)
#let status-mark(status, bullet) = {
  let (class, mark) = if status == none { ("bullet", if bullet { "•" } else { none }) }
    else { (status, status-marks.at(status).mark) }
  if mark == none { [] }
  else {
    on-html(
      () => element("span", "mark " + class, mark),
      () => if status == none { std.text(font: mark-font, fill: luma(110), mark) }
        else { std.text(font: mark-font, fill: status-marks.at(status).colour, weight: "bold", mark) })
  }
}

// the conditions left to a Proof block, [2.1]
#let conditions-left(conditions) = {
  if conditions == none { [] }
  else {
    on-html(
      () => element("span", "conditions", [\[#conditions\] ]),
      () => std.text(size: 0.8em, fill: status-marks.todo.colour, [\[#conditions\] ]))
  }
}

// [mark(status, conditions)]: the status of a span or a div of a checked
// text, inline at the start of its text: its mark, smaller, then the
// conditions left
#let mark(status, conditions: none) = on-html(
  () => element("span", "mark inline " + status, status-marks.at(status).mark)
    + conditions-left(conditions),
  () => box(std.text(size: 0.8em, status-mark(status, false))) + h(0.15em)
    + conditions-left(conditions))

// cyp's message about a node, in a tinted box
#let message-box(status, message) = {
  let colour = status-marks.at(status).colour
  on-html(
    () => element("div", "message " + status, message),
    () => block(above: 0.4em, below: 0.6em, inset: (x: 0.6em, y: 0.35em), radius: 2pt,
      fill: colour.lighten(90%), stroke: (left: 1.5pt + colour),
      std.text(size: 0.85em, message)))
}

// one line of the PDF: its number (when numbers are shown, at the
// margin), then, indented by depth levels, its mark and its text.  The
// mark stands in the first line of the text (so that it is on the line's
// baseline, whatever the script), the next lines hang after it; the grid
// puts its columns from the right, and the hanging indent is at the
// right, in a text written from right to left.
#let mark-width = 1.3em
#let text-line(depth, number, status, bullet, conditions, body) = context {
  let mark = box(width: mark-width, status-mark(status, bullet))
  let numbered = show-numbers.get()
  let label = if number == none { [] } else { std.text(size: 0.75em, fill: luma(130), number) }
  let columns = (if numbered { (3.4em,) } else { () }) + (depth * step-indent, 1fr)
  let cells = (if numbered { (label,) } else { () }) + ([],
    par(hanging-indent: mark-width)[#mark#conditions-left(conditions)#body])
  block(above: 0.6em, below: 0.6em,
    grid(columns: columns, align: start + top, ..cells))
}

// [blocks-at(blocks, depth, inner)]: the blocks of a node, their
// paragraphs at the depth depth (where the text of the node is), its
// lists of items at the depth inner
#let blocks-at(blocks, depth, inner) = for b in blocks {
  if b.kind == "paragraph" {
    on-html(() => element("p", "para", b.body),
      () => text-line(depth, none, none, false, none, b.body))
  } else if b.kind == "message" {
    context {
      let numbered = show-numbers.get()
      let start = (if numbered { 3.4em } else { 0em }) + depth * step-indent + mark-width
      on-html(() => message-box(b.status, b.text), () => pad-start(start, message-box(b.status, b.text)))
    }
  } else if b.kind == "division" {
    on-html(
      () => html.elem("div", attrs: (class: "p", data-id: b.number), blocks-at(b.blocks, depth, inner)),
      () => blocks-at(b.blocks, depth, inner))
  } else if b.kind == "steps" {
    on-html(
      () => element("ul", "steps", for s in b.steps {
        html.elem("li", attrs: (class: "step p", data-id: s.number), context {
          if show-numbers.get() { element("span", "number", s.number) }
          status-mark(s.status, true)
          conditions-left(s.conditions)
          s.body
          blocks-at(s.rest, depth + 1, inner + 1)
        })
      }),
      () => for s in b.steps {
        text-line(inner, s.number, s.status, true, s.conditions, s.body)
        blocks-at(s.rest, inner, inner + 1)
      })
  }
}

// a paragraph of a node
#let paragraph(body) = (kind: "paragraph", body: body)

// cyp's message about a node of status status (ko or todo), where cyp
// wrote it: after the paragraph where the node starts
#let message(status, text) = (kind: "message", status: status, text: text)

// a list of items, each a step
#let steps(list) = (kind: "steps", steps: list)

// an item: its number (Dewey notation, the numbers of the nodes and of
// cyp's conditions), its first paragraph, its other blocks (its
// sub-items, its closing paragraph); in a checked text its status and
// the conditions left to a Proof block
#let step(number, body, rest, status: none, conditions: none) = (
  number: number, body: body, rest: rest, status: status, conditions: conditions)

// a div, ::: p ... :::, of number number: its blocks
#let division(number, blocks) = (kind: "division", number: number, blocks: blocks)

// a span, [ ... ]{.p}, of number number, in the text of a paragraph
#let node(number, body) = on-html(
  () => html.elem("span", attrs: (class: "p", data-id: number), body),
  () => body)

// [proof(statement, blocks, status, conditions)]: the top node: the
// statement (its first paragraph), then its blocks, with its status in a
// checked text.  In the web page, the script of the hover follows it
#let proof(statement, blocks, status: none, conditions: none) = on-html(
  () => {
    html.elem("div", attrs: (class: "p", data-id: "0"), {
      element("p", "statement", status-mark(status, false) + conditions-left(conditions) + statement)
      blocks-at(blocks, 0, 0)
    })
    html.elem("script", hover-script)
  },
  () => {
    text-line(0, none, status, false, conditions, statement)
    v(0.5em)
    blocks-at(blocks, 0, 0)
  })

// ------------------------------------------------------------------
// The legend

// [legend(roles, statuses)]: the key of the look, at the end of the text:
// each role's word (in the language of the text) with the look of the
// role, then, for a text checked by cyp, each status mark with its
// meaning; roles and statuses are lists of (role or status, word) pairs.
// On the web page each role is a switch (a check box) that turns its
// colour on and off; in the PDF only the shown roles are listed
#let legend(roles, statuses: ()) = on-html(
  () => html.elem("footer", attrs: (class: "legend"), {
    for (role, word) in roles {
      let box-attrs = (type: "checkbox", id: "show-" + role)
      if role in shown-roles { box-attrs.insert("checked", "") }
      element("span", "entry", html.elem("label", {
        html.elem("input", attrs: box-attrs)
        element("span", "formula " + role, word)
      }))
    }
    for (status, word) in statuses {
      element("span", "entry", status-mark(status, false) + word)
    }
  }),
  () => block(above: 2em, {
    line(length: 30%, stroke: 0.4pt + luma(190))
    set std.text(size: 0.75em, fill: luma(70))
    (roles.filter(((role, word)) => role in shown-roles)
      .map(((role, word)) => role-look(role, word, cue: true))
      + statuses.map(((status, word)) => box(status-mark(status, false)) + " " + word))
      .join(h(1.4em))
  }))
