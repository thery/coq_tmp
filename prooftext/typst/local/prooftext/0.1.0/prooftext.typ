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
  by: rgb("#d9a9cb"),
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
  by: (line: "underline", dash: "solid"),
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

// the style sheet of an HTML page: the backgrounds and marks of the roles
// and the colours of the statuses (those of the PDF), the indentation of
// the steps, the links, the legend
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
    ".by { color: #5a5a5a; }",
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

// a name used in the text ("by h4", "Applying h2 to h4"), linked to the
// step that introduced it (its label target)
#let named(text, target) = linked(std.label(target), raw(text))

// a lemma, a constructor or a type named in the text ("Applying
// f_equal_nat"), linked to its entry in the documentation of its library
#let cited(text, url) = linked(url, raw(text))

// the justification of a step, by X: X linked to the documentation of
// the lemma (url) or to the step that introduced the name X (target)
#let by(text, url: none, target: none) = {
  let destination = if url != none { url } else if target != none { std.label(target) } else { none }
  // the name in the justification's colour (a role, "by", as a formula's)
  let name = linked(destination, raw(text))
  on-html(
    () => element("span", "by", [#emph[by] #element("span", "formula by", name)]),
    () => [#emph[by] #role-look("by", name)])
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
