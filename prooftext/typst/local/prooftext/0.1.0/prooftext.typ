// prooftext: the look of a proof text in Typst.
//
// A proof text (../../../../README.md) written in Typst by the writer
// write-typst (prooftext/typst.elpi) is a call of the functions below:
//
//   #import "@local/prooftext:0.1.0": *
//   #show: proof-text.with(lang: "en", numbers: false)
//   #title-block("and_swap", (("require", "From Stdlib Require Import Lia."),))
//   #statement[#"Let "#var($A, B : "Prop"$)#". We prove "#claim($B ∧ A$)#"."]
//   #steps((
//     step("1", [#"Assume "#hyp($A ∧ B$)#" "#name("h")#"."], (
//       step("1.1", [...], (), status: "ko", message: "not proved: B /\\ A"),
//     )),
//   ))
//
// Each formula is shown as mathematics (or as Rocq code, monospace, when
// it is given as a string: #claim("B /\\ A")), in the style of its role;
// the steps are indented by their depth; the status of a step (in a text
// checked by cyp) is a coloured mark in front of it.

// ------------------------------------------------------------------
// Colours and fonts

// the colour of each role of a formula, and of a formula without a role
#let role-colours = (
  var: rgb("#1f5fa8"),
  hyp: rgb("#9a5b00"),
  claim: rgb("#1d7a33"),
  fact: rgb("#6b4f96"),
  plain: rgb("#333333"),
)

// the background of the formulas of a role (none: no background)
#let role-backgrounds = (
  var: none,
  hyp: rgb("#fdf1dc"),
  claim: rgb("#e3f4e6"),
  fact: none,
  plain: none,
)

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

// the style sheet of an HTML page: the colours of the roles and of the
// statuses (those of the PDF), the indentation of the steps
#let html-style = {
  let rules = (
    ".proof-text { font-family: 'Libertinus Serif', 'Noto Serif', serif; max-width: 48em; margin: 2em auto; padding: 0 1em; line-height: 1.6; }",
    ".proof-text code { font-family: 'DejaVu Sans Mono', monospace; font-size: 0.9em; }",
    ".proof-text math { font-family: 'Latin Modern Math', 'STIX Two Math', math; }",
    ".proof-text header h1 { font-size: 1.5em; margin-bottom: 0.3em; }",
    ".proof-text table.fields { font-size: 0.8em; color: #505050; border-bottom: 1px solid #b4b4b4; padding-bottom: 0.5em; width: 100%; }",
    ".proof-text table.fields th { text-align: start; padding-inline-end: 0.8em; vertical-align: top; width: 1%; white-space: nowrap; }",
    ".formula { border-radius: 2px; padding: 0 1px; }",
    ".formula.fact { text-decoration: underline dotted; }",
    ".name { color: " + role-colours.hyp.to-hex() + "; font-size: 0.9em; }",
    ".by { color: #5a5a5a; }",
    "ul.steps { list-style: none; padding-inline-start: " + repr(step-indent) + "; margin: 0; }",
    ".proof-text > ul.steps { padding-inline-start: 0; }",
    "li.step, p.statement { margin: 0.5em 0; }",
    ".mark { display: inline-block; width: 1.3em; font-family: 'DejaVu Sans', sans-serif; font-weight: bold; color: #6e6e6e; }",
    ".number { color: #828282; font-size: 0.75em; margin-inline-end: 0.6em; }",
    ".conditions { color: " + status-marks.todo.colour.to-hex() + "; font-size: 0.8em; }",
    ".message { margin: 0.4em 0 0 1.3em; padding: 0.35em 0.6em; font-size: 0.85em; border-inline-start: 2px solid; border-radius: 2px; }",
  )
  for (role, colour) in role-colours {
    let background = role-backgrounds.at(role)
    rules.push(".formula." + role + " { color: " + colour.to-hex() + ";"
      + (if background == none { "" } else { " background: " + background.to-hex() + ";" }) + " }")
  }
  for (status, s) in status-marks {
    rules.push(".mark." + status + " { color: " + s.colour.to-hex() + "; }")
    rules.push(".message." + status + " { border-color: " + s.colour.to-hex()
      + "; background: " + s.colour.lighten(90%).to-hex() + "; }")
  }
  rules.join("\n")
}

// ------------------------------------------------------------------
// The parts of the text of a step

// a formula of role Role ("var", "hyp", "claim", "fact" or "plain"):
// mathematics (content, $...$, printed from its Rocq term), or its text
// in Rocq syntax (a string), shown as code
#let formula-of(role, body) = {
  let written = if type(body) == str { raw(body) } else { body }
  on-html(
    () => element("span", "formula " + role, written),
    () => {
      let shown = std.text(fill: role-colours.at(role), written)
      let background = role-backgrounds.at(role)
      let highlighted = if background == none { shown }
        else { highlight(fill: background, extent: 1pt, radius: 2pt, shown) }
      // a fact is a mention: underlined, so that it differs from a
      // variable without its colour
      if role == "fact" {
        underline(stroke: (paint: role-colours.fact, thickness: 0.5pt, dash: "dotted"),
          offset: 2pt, highlighted)
      } else { highlighted }
    })
}

// a variable, a hypothesis, a claim, a fact, a formula without a role
#let var(body) = formula-of("var", body)
#let hyp(body) = formula-of("hyp", body)
#let claim(body) = formula-of("claim", body)
#let fact(body) = formula-of("fact", body)
#let formula(body) = formula-of("plain", body)

// the name given to the formula before it (a hypothesis, a claim), (h)
#let name(text) = on-html(
  () => element("span", "name", [(#raw(text))]),
  () => std.text(fill: role-colours.hyp, size: 0.9em,
    [(#std.text(font: code-fonts, text))]))

// the justification of a step, by X
#let by(text) = on-html(
  () => element("span", "by", [#emph[by] #raw(text)]),
  () => std.text(fill: luma(90), [#emph[by] #raw(text)]))

// ------------------------------------------------------------------
// The document

// [proof-text(lang, numbers, body)]: the page and the fonts of the text in
// the language lang; numbers: the numbers of the steps are shown (those
// of cyp's conditions, in Dewey notation)
#let show-numbers = state("prooftext-numbers", false)
#let proof-text(lang: "en", numbers: false, body) = {
  set text(lang: lang, dir: if lang in rtl-languages { rtl } else { ltr })
  show-numbers.update(numbers)
  on-html(
    () => {
      html.elem("style", html-style)
      html.elem("div", attrs: (class: "proof-text", lang: lang,
        dir: if lang in rtl-languages { "rtl" } else { "ltr" }), body)
    },
    () => {
      set page(paper: "a4", margin: (x: 2cm, y: 2cm), numbering: "1")
      set text(font: (latin-font,) + language-fonts.at(lang, default: ()) + text-fonts,
        size: 10.5pt)
      // the formulas as Rocq code are written from left to right in every
      // language
      show raw: set text(font: code-fonts, size: 0.92em, dir: ltr)
      set par(justify: false, leading: 0.7em)
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

// The status of a step is that of a text checked by cyp, with cyp's names
// (its .cyp.json): "ok", "ko", "todo", "none" (nothing to check in the
// step); a text that is not checked has none (the value), and its steps a
// bullet.

// the mark in front of a step of status status, a bullet for a step that
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

// cyp's message under a step that it did not prove
#let step-message(status, message) = {
  if message == none { [] }
  else {
    let s = if status == none { "none" } else { status }
    let colour = status-marks.at(s).colour
    on-html(
      () => element("div", "message " + s, message),
      () => block(above: 0.4em, inset: (x: 0.6em, y: 0.35em), radius: 2pt,
        fill: colour.lighten(90%), stroke: (left: 1.5pt + colour),
        std.text(size: 0.85em, message)))
  }
}

// the conditions left to a Proof block, [2a, 2b]
#let conditions-left(conditions) = {
  if conditions == none { [] }
  else {
    on-html(
      () => element("span", "conditions", [\[#conditions\] ]),
      () => std.text(size: 0.8em, fill: status-marks.todo.colour, [\[#conditions\] ]))
  }
}

// one line of the PDF: its number (when numbers are shown, at the
// margin), then, indented by depth levels, its mark, its text and cyp's
// message.  The mark stands in the first line of the text (so that it is
// on the line's baseline, whatever the script), the next lines hang
// after it; the grid puts its columns from the right, and the hanging
// indent is at the right, in a text written from right to left.
#let mark-width = 1.3em
#let text-line(depth, number, status, bullet, conditions, message, body) = context {
  let mark = box(width: mark-width, status-mark(status, bullet))
  let numbered = show-numbers.get()
  let label = if number == none { [] } else { std.text(size: 0.75em, fill: luma(130), number) }
  let columns = (if numbered { (3.4em,) } else { () }) + (depth * step-indent, 1fr)
  let cells = (if numbered { (label,) } else { () }) + ([],
    par(hanging-indent: mark-width)[#mark#conditions-left(conditions)#body]
    + if message != none { pad-start(mark-width, step-message(status, message)) })
  block(above: 0.6em, below: 0.6em,
    grid(columns: columns, align: start + top, ..cells))
}

// the statement of the theorem, with its status in a checked text
#let statement(body, status: none, conditions: none, message: none) = on-html(
  () => {
    element("p", "statement",
      status-mark(status, false) + conditions-left(conditions) + body)
    step-message(status, message)
  },
  () => {
    text-line(0, none, status, false, conditions, message, body)
    v(0.5em)
  })

// a step: its number (Dewey notation, the numbers of cyp's conditions),
// its text and its sub-steps; in a checked text its status, the
// conditions left to a Proof block and cyp's message
#let step(number, body, sub, status: none, conditions: none, message: none) = (
  number: number, body: body, sub: sub, status: status,
  conditions: conditions, message: message)

// [steps(list)]: the steps, each with its sub-steps below it, one level
// further in (in HTML, nested lists)
#let steps(list, depth: 0) = on-html(
  () => if list.len() > 0 {
    element("ul", "steps", for s in list {
      element("li", "step", context {
        if show-numbers.get() { element("span", "number", s.number) }
        status-mark(s.status, true)
        conditions-left(s.conditions)
        s.body
        step-message(s.status, s.message)
        steps(s.sub, depth: depth + 1)
      })
    })
  },
  () => for s in list {
    text-line(depth, s.number, s.status, true, s.conditions, s.message, s.body)
    steps(s.sub, depth: depth + 1)
  })
