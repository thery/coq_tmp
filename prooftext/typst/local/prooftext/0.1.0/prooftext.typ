// prooftext: the look of a proof text in Typst.
//
// A proof text (../../../../README.md) written in Typst by the writer
// write-typst (prooftext/typst.elpi) is a call of the functions below:
//
//   #import "@local/prooftext:0.1.0": *
//   #show: proof-text.with(lang: "en", numbers: false)
//   #title-block("and_swap", (("require", "From Stdlib Require Import Lia."),))
//   #statement(none)[#"Let "#var("A B : Prop")#". We prove "#claim("B /\\ A")#"."]
//   #steps((
//     step("1", "ok", [#"Assume "#hyp("A /\\ B")#" "#name("h")#"."], (
//       step("1.1", "ko", [...], (), message: "not proved: B /\\ A"),
//     )),
//   ))
//
// Each formula is shown as Rocq code (monospace), in the style of its
// role; the steps are indented by their depth; the status of a step (in a
// text checked by cyp) is a coloured mark in front of it.

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
// The parts of the text of a step

// a formula of role Role ("var", "hyp", "claim", "fact" or "none"), its
// text in Rocq syntax shown as code
#let formula-of(role, text) = {
  let shown = std.text(fill: role-colours.at(role), raw(text))
  let background = role-backgrounds.at(role)
  if background == none { shown }
  else { highlight(fill: background, extent: 1pt, radius: 2pt, shown) }
}

// a variable, a hypothesis, a claim, a fact, a formula without a role
#let var(text) = formula-of("var", text)
#let hyp(text) = formula-of("hyp", text)
#let claim(text) = formula-of("claim", text)
#let fact(text) = {
  // a fact is a mention: underlined, so that it differs from a
  // variable without its colour
  underline(stroke: (paint: role-colours.fact, thickness: 0.5pt, dash: "dotted"),
    offset: 2pt, formula-of("fact", text))
}
#let formula(text) = formula-of("plain", text)

// the name of a hypothesis, (h)
#let name(text) = std.text(fill: role-colours.hyp, size: 0.9em,
  [(#std.text(font: code-fonts, text))])

// the justification of a step, by X
#let by(text) = std.text(fill: luma(90), [#emph[by] #raw(text)])

// ------------------------------------------------------------------
// The document

// [proof-text(lang, numbers, body)]: the page and the fonts of the text in
// the language lang; numbers: the numbers of the steps are shown (those
// of cyp's conditions, in Dewey notation)
#let show-numbers = state("prooftext-numbers", false)
#let proof-text(lang: "en", numbers: false, body) = {
  set page(paper: "a4", margin: (x: 2cm, y: 2cm), numbering: "1")
  set text(lang: lang, dir: if lang in rtl-languages { rtl } else { ltr },
    font: (latin-font,) + language-fonts.at(lang, default: ()) + text-fonts,
    size: 10.5pt)
  // the formulas are Rocq code, written from left to right in every
  // language
  show raw: set text(font: code-fonts, size: 0.92em, dir: ltr)
  set par(justify: false, leading: 0.7em)
  show-numbers.update(numbers)
  body
}

// [title-block(name, fields)]: the name of the theorem, and the fields of
// the header (key, value) in a small table
#let title-block(name, fields) = {
  block(below: 1.2em, {
    std.text(size: 1.5em, weight: "bold", raw(name))
    if fields.len() > 0 {
      v(0.4em)
      set std.text(size: 0.8em, fill: luma(80))
      grid(columns: (auto, 1fr), column-gutter: 0.8em, row-gutter: 0.45em,
        ..fields.map(((key, value)) => (strong(key), raw(value))).flatten())
    }
    v(0.3em)
    line(length: 100%, stroke: 0.5pt + luma(180))
  })
}

// The status of a step is that of a text checked by cyp, with cyp's names
// (its .cyp.json): "ok", "ko", "todo", "none" (nothing to check in the
// step); a text that is not checked has none (the value), and its steps a
// bullet.

// the mark in front of a step of status status, a bullet for a step that
// is not checked (and nothing for a statement that is not checked)
#let status-mark(status, bullet) = {
  if status == none { if bullet { std.text(fill: luma(110), "•") } else { [] } }
  else {
    let s = status-marks.at(status)
    std.text(fill: s.colour, weight: "bold", s.mark)
  }
}

// cyp's message under a step that it did not prove
#let step-message(status, message) = {
  if message == none { [] }
  else {
    let colour = status-marks.at(if status == none { "none" } else { status }).colour
    block(above: 0.4em, inset: (x: 0.6em, y: 0.35em), radius: 2pt,
      fill: colour.lighten(90%), stroke: (left: 1.5pt + colour),
      std.text(size: 0.85em, message))
  }
}

// one line of the text: its number (when numbers are shown, at the
// margin), then, indented by depth levels, its mark, its text and cyp's
// message.  The mark stands in the first line of the text (so that it is
// on the line's baseline, whatever the script), the next lines hang
// after it; the grid puts its columns from the right, and the hanging
// indent is at the right, in a text written from right to left.
#let mark-width = 1.3em
#let text-line(depth, number, status, bullet, conditions, message, body) = context {
  let mark = box(width: mark-width, status-mark(status, bullet))
  let conditions-left = if conditions == none { [] } else {
    std.text(size: 0.8em, fill: status-marks.todo.colour, [\[#conditions\] ])
  }
  let numbered = show-numbers.get()
  let label = if number == none { [] } else { std.text(size: 0.75em, fill: luma(130), number) }
  let columns = (if numbered { (3.4em,) } else { () }) + (depth * step-indent, 1fr)
  let cells = (if numbered { (label,) } else { () }) + ([],
    par(hanging-indent: mark-width)[#mark#conditions-left#body]
    + if message != none { pad-start(mark-width, step-message(status, message)) })
  block(above: 0.6em, below: 0.6em,
    grid(columns: columns, align: start + top, ..cells))
}

// the statement of the theorem, with its status in a checked text
#let statement(body, status: none, conditions: none, message: none) = {
  text-line(0, none, status, false, conditions, message, body)
  v(0.5em)
}

// a step: its number (Dewey notation, the numbers of cyp's conditions),
// its text and its sub-steps; in a checked text its status, the
// conditions left to a Proof block and cyp's message
#let step(number, body, sub, status: none, conditions: none, message: none) = (
  number: number, body: body, sub: sub, status: status,
  conditions: conditions, message: message)

// [steps(list)]: the steps, each with its sub-steps below it, one level
// further in
#let steps(list, depth: 0) = {
  for s in list {
    text-line(depth, s.number, s.status, true, s.conditions, s.message, s.body)
    steps(s.sub, depth: depth + 1)
  }
}
