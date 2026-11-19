// Mock-up of the proposed rendering (PROPOSAL.md), on top of today's
// template.  Hand-written: no reader produced these files.
#import "@local/prooftext:0.1.0": *

// The colour of a justification: the template's role "by" (the user's
// fifth role colour, on main since 76b314b), with role-look as a
// formula's; no "by" is added: the word, if any, is in the text
#let jb(body) = role-look("by", if type(body) == str { raw(body) } else { body })

// ---- the structured syntax: one line per proof node, and the closing
// paragraph after the sub-proofs, at the text of its item
#let item(depth, body) = text-line(depth, none, none, true, none, none, body)
#let closing(depth, body) = text-line(depth, none, none, false, none, none, body)

// ---- the free syntax: a proof node is a span of a paragraph; with
// brackets on, a thin bar in the left margin covers its lines, one bar
// per depth
#let structure-mode = sys.inputs.at("brackets", default: "on")
#let show-brackets = structure-mode == "on"
#let corner(c) = std.text(font: mark-font, fill: luma(140), size: 0.8em, c)
#let ps(id, depth, body) = {
  [#metadata((id: id, depth: depth))<pstart>]
  if structure-mode == "corners" { corner("⌜") }
  body
  if structure-mode == "corners" { corner("⌟") }
  [#metadata((id: id, depth: depth))<pend>]
}

#let bracket-layer = context {
  if not show-brackets { return }
  let page = here().page()
  for s in query(<pstart>) {
    let e = query(<pend>).find(m => m.value.id == s.value.id)
    let a = s.location().position()
    let b = e.location().position()
    if a.page != page { continue }
    let x = 2cm - 0.35cm - s.value.depth * 0.18cm
    let y1 = a.y - 0.75em
    let y2 = if b.page == page { b.y + 0.3em } else { 29.7cm - 2cm }
    place(top + left, dx: x, dy: y1,
      line(start: (0pt, 0pt), end: (0pt, y2 - y1), stroke: 0.6pt + luma(150)))
    place(top + left, dx: x, dy: y1, line(length: 0.12cm, stroke: 0.6pt + luma(150)))
    place(top + left, dx: x, dy: y2, line(length: 0.12cm, stroke: 0.6pt + luma(150)))
  }
}

// a free paragraph (the text of the top proof node)
#let prose(body) = block(above: 0.8em, below: 0.8em, par(leading: 0.9em, body))

// the section heading of an example in the mock-up
#let example(name, note) = {
  v(0.8em)
  std.text(size: 1.25em, weight: "bold", raw(name))
  h(0.6em)
  std.text(size: 0.8em, fill: luma(110), note)
  v(0.2em)
}

#let legend5 = block(above: 2em, {
  line(length: 30%, stroke: 0.4pt + luma(190))
  set std.text(size: 0.75em, fill: luma(70))
  ((("var", "variable"), ("hyp", "hypothesis"), ("claim", "conclusion"), ("fact", "fact"))
    .map(((role, word)) => role-look(role, word, cue: true)) + (role-look("by", [justification], cue: true),)).join(h(1.4em))
})
