# prooftext: the format of proof texts

A *proof text* is a proof written as a Markdown file, with its formulas in
Rocq syntax.  Two tools share the format: [xtext](../xtext/README.md)
writes proof texts from Rocq proofs, [cyp](../cyp/README.md) reads them and
checks them step by step.  This library holds what the two must agree on,
so that each tool does not keep its own copy: the document tree and its
writer, the header and its fields, how a formula carries its role, how a
step names its justification, fresh names, and the tactics a text may
name.  The words of the texts (the phrases of each language) are in the
[lexicon](../lexicon/README.md).

## Loading

```coq
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From Lexicon Extra Dependency "lang_en.elpi" as lex_en.   (* and the other tables *)
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "names.elpi" as pt_names.
From ProofText Extra Dependency "tactics.elpi" as pt_tactics.
From ProofText Extra Dependency "checked.elpi" as pt_checked.
From ProofText Extra Dependency "maths-table.elpi" as pt_maths_table.
From ProofText Extra Dependency "maths.elpi" as pt_maths.
From ProofText Extra Dependency "maths-typst.elpi" as pt_maths_typst.
From ProofText Extra Dependency "links.elpi" as pt_links.
From ProofText Extra Dependency "typst.elpi" as pt_typst.
Elpi Accumulate File lex_core lex_en pt_header pt_document pt_formulas pt_names pt_tactics
  pt_checked pt_maths_table pt_maths pt_maths_typst pt_links pt_typst.
```

with `-Q prooftext ProofText` and `-Q lexicon Lexicon`.  `lexicon.elpi`
comes first (`formulas.elpi` uses its roles), `header.elpi` before
`document.elpi`, `document.elpi` before `checked.elpi`, the table of
notations, `maths-table.elpi`, before the printer, `maths.elpi`, before its
Typst writer, `maths-typst.elpi`, then `links.elpi` and `typst.elpi`
last (they use the tables of the lexicon, `lang_xx.elpi`, for the words of
the texts and of the legend).  A tool loads only the files it uses.  Every name is in the namespace `prooftext`
(`prooftext.write-document`, `prooftext.step`, ...), so that it does not
meet the names of the tools.

Tests: `rocq c -Q ../lexicon Lexicon -Q . ProofText check.v`; those of the
printer of formulas, `check_maths.v` (the same command); those of the
Typst back end, `sh typst/check.sh` (below, "The PDF of a proof text").

## The format

```markdown
---
require: From Stdlib Require Import Arith Lia. Require Import MyFile.
by: tauto | lia
---

# and_swap

Let `A B : Prop`{.var}. We prove `A /\ B -> B /\ A`{.claim}.

- Assume `A /\ B`{.hyp} (h).
  - We have `B /\ A`{.claim} *by tauto*.
- We have proved `A /\ B -> B /\ A`{.claim}.
```

- the **header**, between two lines `---`, one field `key: value` per line;
- the **title**, `# name`, the name of the theorem;
- the **statement**, the text between the title and the first step;
- the **steps**, a nested Markdown list: a step's sub-steps are the items
  indented below it;
- in the text of a statement or a step, each **formula** between
  backticks, with its role as a Pandoc class right after it, and the
  **justification** of a step, `*by X*`.

## The files

- `header.elpi`: the type `field` (`field Key Value`); `header-key Key`,
  the keys a header may have:

  | key | meaning |
  |---|---|
  | `require` | the Rocq commands run before the proof: the libraries, and the file of the lemmas it uses |
  | `rules` | the files of rules (`.elpi`, `.v`) that the reader adds to its own |
  | `flags` | options of `rocq c` for the reader's driver (load paths `-Q`, `-R`, `-I`) |
  | `scope` | the notation scope in which the formulas are read |
  | `lang` | the language of the text (`default-lang`, `en`, when there is none) |
  | `by` | the default tactics of the proof, tried on a step that names none, separated by `|` |
  | `gaps` | `off`: the reader tries no gap tactic on the conditions left open (cyp) |

  and the writing of a header: `header-lines Fields Lines` (a key that
  is not a `header-key` is an error), `lang-fields Lang Fields` (no field
  for the default language), `by-field Tactics Field`, and its reading:
  `field-value Fields Key Value` (`""` for a field the header has not),
  `header-lang Fields Lang` (`default-lang` without a `lang` field);
- `document.elpi`: the document tree, `document Fields Name Place
  Statement Steps`, a step `step Place Text Sub-steps`, a `place` (`lines
  First Last`, the lines of a text in its file, numbered from 0, given by
  a reader; `unplaced` for a text being written), the writer
  `write-document D Text`, a reader, `read-document File D` (the
  reader's contract below; cyp's and the Typst writer's), and the number
  of a step, `step-number Parent K Number` (Dewey notation, `2.1` the
  first sub-step of step 2: cyp numbers its conditions with it, the Typst
  writer its steps);
- `checked.elpi`: what a checker adds to the text of a step (cyp's
  `.checked.md`): `status-mark Status Mark` (`ok` ✅, `ko` ❌, `todo` 🔶,
  `none` ▫️, cyp's names of the statuses), `message-block M S` (the
  folded block `<details><summary>M</summary></details>` under a step),
  `conditions-mark Ids S` (`**[2a, 2b]**`, the conditions left to a Proof
  block), and their reading, `split-checked Text (checked Status
  Conditions Message) Rest`.  cyp writes its marks with these predicates;
- `typst.elpi`: the Typst writer, `write-typst D Text` (formulas in
  mathematics), `write-typst-in Style D Text` (`maths` or `code`), and
  `write-as File D Text` (Typst for a file `.typ`, Markdown otherwise);
  see "The PDF of a proof text";
- `links.elpi`: the links of the PDF and of the web page: `name-label
  Where Name Label`, the label of the step that introduces a name,
  `documentation-url Name Url`, the documentation of a lemma, from
  `library-documentation Root Base`, `text-pieces Text Pieces`, the words
  of a text, and `lexicon-words Lang Words`, the words of the lexicon,
  which are never names; see "Links";
- `maths-table.elpi`, `maths.elpi`, `maths-typst.elpi`: the formulas as
  mathematics, the table of notations, the printer of Rocq terms and its
  Typst writer; see "Formulas as mathematics";
- `formulas.elpi`: `role-tag Role Tag` (`rvar` `var`, `rhyp` `hyp`,
  `rclaim` `claim`, `rfact` `fact`, and `rback`, a claim that replaces
  the goal, written as a claim: read back, the class `claim` gives
  `rclaim`, the first role with it), `formula Role F S` (`` `F`{.tag} ``),
  `justification J S` (`*by J*`), `is-justification S`, the reading
  of a step's justification, `split-justification S J Rest`, and the
  reading of the text of a statement or a step, `text-parts Text Parts`
  (below, the reader's contract), the one reader of cyp and of the Typst
  writer;
- `names.elpi`: `fresh-name Used Wanted Name`, `Wanted` if it is not in
  use, else `Wanted0`, `Wanted1`, ...: the names a text introduces must
  differ from the names in use, so that `*by h*` names one hypothesis
  (xtext names its binders with it, `binder-name` in
  `xtext/elpi/printing.elpi`; cyp can name its hypotheses with it);
- `tactics.elpi`: `tactic Name`, the tactics a text may name in `*by X*`
  or in its `by` field, and `unknown-tactics Names Unknown`.  Each tool
  runs a name its own way: cyp runs the Ltac definition `cyp_Name`
  (`cyp/vernac/Cyp.v`; the rules of a proof may add tactics,
  `tactic-name Name Ltac`); xtext writes only these
  names (the text of its tactics, `xtext-tactic Ltac Name` and
  `xtext-guard-tactic Ltac Name` in `xtext/Explain.v`, which run them with
  a time limit), and `xtext/vocab_check.v` checks it.  A name added to one
  tool's table goes here first.

## Writing a proof text

`write-document (document Fields Name _ Statement Steps) Text` gives the
header lines, an empty line, `# Name`, an empty line, the statement on one
line, an empty line, then one line per step, `- Text`, the sub-steps of a
step below it with two more spaces of indentation; `Text` ends with a
newline.  The places are not used.  A writer gives each step its text in
one line; xtext also ends each with a punctuation mark.

## Reading a proof text (the reader's contract)

A reader gives, from the lines of a file (numbered from 0), the same
`document`, with places (`read-document` in `document.elpi`, the reader
of cyp and of the Typst back end):

- **header**: if the first line is `---` (spaces around it ignored), the
  lines up to the next line `---` are fields; a field line is `key:
  value`, spaces before the key and around the value ignored.  The keys
  that have a meaning are the `header-key`s; a reader ignores the others.
  Without a first line `---`, the header is empty;
- **title**: the first line after the header that starts with `# `; the
  rest of the line, trimmed, is the name;
- **statement**: the lines between the title and the first item that are
  not empty, trimmed and joined by one space; its place is that of its
  first and last lines (`lines 0 0` when there is none);
- **steps**: an item is a line that starts, after spaces, with `- ` or
  `* `.  Its text is the rest of the line and the lines after it up to
  the next item (continuation lines), trimmed, the empty ones left out,
  joined by one space; its place is its first line and its last
  continuation line.  Its indentation is the number of spaces before
  `-`; its sub-steps are the items after it with a larger indentation, up
  to the first item that has not;
- within the text of a statement or a step (`text-parts` in
  `formulas.elpi`): a **formula** is the text between two backticks (a
  backtick with no other after it is text); right after it may come its
  **class**, `{.tag}` (letters; a class that is no role's tag gives no
  role, but is not text either), then, after any number of spaces, the
  **name** given to it, `(h)` (an identifier); the **justification** is
  `*by X*`.  A part is `plain Words`, `formula-part Class Formula Name`
  (`Name` is `some h` or `none`) or `by-part X`.  The role of a formula is
  that of its class; a formula with no class takes its role from the
  phrases of the lexicon around it (cyp: `cyp/vernac/elpi/text.elpi`).
  A name after a hypothesis names it; after a fact it is the name of the
  hypothesis the fact is; after a claim, the name a later step uses (the
  Typst writer links them).

What a document written by `write-document` gives when read back is the
same document, with places.

## The PDF of a proof text (Typst)

```sh
prooftext/pdf.sh xtext/examples/or_commut.md          # or_commut.typ, then or_commut.pdf
prooftext/pdf.sh xtext/cyp-check/half_le.checked.md   # a text checked by cyp, with its statuses
prooftext/pdf.sh foo.typ                              # a text xtext wrote in Typst
prooftext/pdf.sh --code proof.md                      # the formulas as Rocq code, not mathematics
prooftext/pdf.sh --html proof.md                      # an HTML page, proof.html, not a PDF
prooftext/pdf.sh --flags "-R xtext XText" proof.md    # a load path for the require line
prooftext/pdf.sh --source proof.md                    # the Typst source only
prooftext/pdf.sh --links '[["index", "../index.html"]]' proof.typ   # links above the text (gallery.sh)
prooftext/pdf.sh --roles claim,by proof.md   # colour only the claims and justifications (all by default)
sh prooftext/gallery.sh ~/gallery                      # every text of the repository, with an index
```

`pdf.sh` writes the Typst source of each text next to it (`proof.md` gives
`proof.typ`), then its PDF with [Typst](https://typst.app) (0.15).  The
formulas are mathematics: `pdf.sh` runs the `require` line of the text's
header (with the load paths of its `flags` line and of `--flags`) before
the command `Typst`, so that each formula elaborates in Rocq (see
"Formulas as mathematics"); with `--code` they are Rocq code, as written,
and nothing is required.  The command says how many formulas it shows as
code (those that do not elaborate).  It
needs the opam switch `elpi5` and `typst`; it compiles `Typst.vo` when it
is older than its sources.  Typst is installed as a snap here: it reads
and writes only under the home directory, not in `/tmp`.

### How it works, and why there

- **The writer is in Elpi, here**, next to `write-document`:
  `write-typst D Text` (`typst.elpi`) writes the same document tree.  Both
  tools use it.  xtext writes a document it has just built
  (`Explain foo to "foo.typ"`: `write-as` chooses the writer by the
  extension of the file).  A text in Markdown (one that xtext wrote, a
  text checked by cyp, a text written by hand) is first read with
  `read-document`, which follows the reader's contract above.  Reading
  Markdown therefore needs no OCaml driver: the command
  `Typst "proof.md" to "proof.typ".` (`Typst.v`) is a few lines, and
  `pdf.sh` is a shell script that runs it, then `typst`.  pandoc is not
  used: its generic conversion knows neither the roles nor the statuses.
- **The look is in a Typst template**, `typst/local/prooftext/0.1.0/prooftext.typ`.
  It is a local Typst package, `@local/prooftext:0.1.0`, so that a Typst
  source imports it by name, wherever the source is:
  `typst compile --package-path prooftext/typst proof.typ`.  The Typst
  source only calls the template's functions; the colours, fonts and
  spacing are set in one place, the template.

A Typst source (xtext's `and_swap`, shortened):

```typst
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("and_swap", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. ..."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#statement[#"Let "#var($A , B : "Prop"$)#". Assume "#hyp($A ∧ B$)#" "#name("H", label: "statement:H")#". We prove "#claim($B ∧ A$)#"."]

#steps((
  step("1", [#"Going back to the definition of and (match) in "#fact($A ∧ B$)#" "#name("H", target: "statement:H")#", we prove "#claim($B ∧ A$)#":"], (
    step("1.1", [#"Assume "#hyp($A$)#" "#name("a", label: "1.1:a")#" and "#hyp($B$)#" "#name("b", label: "1.1:b")#"."], (
      step("1.1.1", [#"By definition of and ("#cited("conj", "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#conj")#"), ... "#by("Corelib.Init.Logic.conj", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#conj")#"."], ()),
    )),
  )),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("by", "justification"),))
```

The text of a statement or of a step is cut into its parts: the formulas
with their roles, the name `(h)` given to a formula (right after it), the
justification `*by X*`, and the plain text between them, where the names
and the lemmas are links (`named`, `cited`; see "Links").  Each part is
written as a Typst string, so that no character of the text is read as
Typst markup; a formula is Typst maths, `$...$`, made by the printer, or,
as code, a string: `#claim("B /\\ A")`.

### What the PDF shows

- **The header** is a small title block: the name of the theorem, then
  each field of the header (`require`, `flags`, `by`, `lang`, ...) with
  its value as code.
- **Formulas** are mathematics (∀ n ∈ ℕ, n + 0 = n), printed from their
  Rocq terms (see "Formulas as mathematics"); with `--code`, or when a
  formula does not elaborate, Rocq code in a monospace font.  The text of
  every formula is black; its role is given by a light background.  The
  legend at the end of a text also shows, for each role, a mark that needs
  no colour (the template's `role-cues`); the formulas of the text have
  their background only:

  | role | class | background | mark (in the legend) |
  |---|---|---|---|
  | variable | `{.var}` | light sky blue `#d4ebf9` | none |
  | hypothesis | `{.hyp}` | light orange `#f8d49c` | a dashed line under it |
  | claim | `{.claim}` | light yellow `#fcf6c6` | a thin frame |
  | fact (a mention) | `{.fact}` | light grey `#e3e3e3` | a dotted line under it |
  | no class | | none | none |

  The backgrounds are light tints of the Okabe-Ito palette (sky blue,
  orange, yellow; grey), whose colours stay apart for the common kinds
  of colour blindness; there is no red and green pair.  Orange and yellow
  look alike for red-green colour blindness: the hypothesis's tint is
  darker.  The page was checked through the
  simulations of protanopia, deuteranopia and tritanopia (Machado et al.'s
  matrices, ImageMagick's `-color-matrix`, on the PDF and on the web
  page of `drinker`): the four roles stay distinct.  In the PDF a formula
  is a box (Typst's highlights and underlines do not reach the symbols of
  maths); a formula wider than its line is a box as wide as the line,
  where it breaks.

  The name `(h)` of a formula is in black, in monospace.  The
  justification is grey, *by* `X`.  The links are blue (Okabe-Ito blue,
  `#0072b2`): a name and a lemma that link somewhere (see "Links").
- **The steps** are one paragraph each, indented by their depth, with a
  bullet.  A long step wraps under its own text, not under the bullet.
- **A text checked by cyp** has a coloured mark in place of the bullet:
  ✔ green, proved (✅); ✘ red, not proved (❌); ◆ orange, left to a Proof
  block (🔶), with the numbers of the conditions left; ▫ grey, nothing to
  check (▫️).  The statement has its mark too.  cyp's message is in a tinted
  box under the step.  The steps are numbered in the margin, in Dewey
  notation (`2.1` is the first sub-step of `2`), as cyp numbers its
  conditions.  Only a checked text has these numbers: a text that is not
  checked has no use for them.
- **The language** is the `lang` field.  Arabic is written from right to
  left: the bullets, the indentation and the wrapped lines are on the
  right; formulas stay left to right.

### Links

The PDF and the web page have the same links, made with Typst's `link`
and `label` (`links.elpi`, `typst.elpi`, the template's `linked`).  There
are three kinds; the writer finds the first two while it reads the text,
with no table of names.

1. **A name and its uses.**  A name given to a formula, `` `A`{.hyp}
   (h) `` (a hypothesis, or a claim that a later step names, `(P1)`),
   introduces it: the writer gives it a label, `statement:h` or `1.2:h`
   (the number of its step).  Its uses link back to it: the name after a
   fact, `` `A`{.fact} (h) `` (the hypothesis the fact is), a word of the
   text ("By h4 we have", "Applying h2 to h4 and P1", "By IH we have")
   and a justification, `*by h*`.  A name holds where a declaration does
   (a `Let`): in the rest of its step, the step's sub-steps and the steps
   after it in its list; the names of the statement in the whole proof;
   the latest introduction wins.  A word is a name only when it is not a
   word of the lexicon of the text's language, so that "a" in French
   "il y a" never links to a hypothesis `(a)`.  This is the same for the
   texts of xtext and for the texts checked by cyp: both are read by
   `read-document`.
2. **A lemma and its documentation.**  A justification, `*by
   Corelib.Init.Datatypes.nat_ind*`, and a word of the text that Rocq
   locates as a lemma, a constructor or a type ("Applying f_equal_nat",
   "(nat, nat_ind)") link to its entry in the online documentation of
   its library, when the library has one: the corelib and the stdlib
   (`library-documentation`), at
   `https://rocq-prover.org/corelib/<file>.html#<name>` and
   `https://rocq-prover.org/stdlib/<file>.html#<name>`.  The file is the
   library that holds the name (`coq.modpath->library`), the anchor the
   rest of its full name: `Nat.add_succ_r` of `Stdlib.Arith.PeanoNat` is
   `.../stdlib/Stdlib.Arith.PeanoNat.html#Nat.add_succ_r`.  A name is
   located in the context of the command `Typst`, after the `require`
   line of the text (with `--code`, without it: only the names that the
   prelude has, or given in full).  A name of another library (a lemma
   of the user, of xtext's examples) has no link: the gallery does not
   know where its source is published.  A tactic (`*by lia*`) has none.
   Another library adds its documentation with a clause, as the
   notations are added: `prooftext.library-documentation "MyLib"
   "https://.../"`, if its pages follow rocqdoc's scheme.
3. **The pages of a gallery** (`gallery.sh`): see "The gallery".

The addresses without a version, `rocq-prover.org/corelib/...` and
`rocq-prover.org/stdlib/...`, lead to the latest documentation (checked
with `curl` in November 2026: `/corelib/` redirects to `doc/V9.2.0/corelib/`,
`/stdlib/` to `doc/V9.1.0/stdlib/`).  The addresses with the version of
this machine do not all exist: Rocq 9.1.1's corelib does
(`doc/V9.1.1/corelib/`), its stdlib 9.2.0's does not
(`doc/V9.2.0/stdlib/` is a 404).  The pages have one anchor per name
defined in the file (`id="eq_refl"`, `id="nat_ind"`, `id="Nat.eq_equiv"`;
seen in the pages of `Corelib.Init.Logic`, `Corelib.Init.Datatypes`,
`Corelib.Init.Peano`, `Stdlib.Reals.RIneq`, `Stdlib.Arith.PeanoNat`).  A
name that a file gets from a functor (`Nat.add_succ_r`, `Nat.lt_eq_cases`
in `PeanoNat`, made by `Include`) has no anchor: its link leads to the
top of the page of its file.

In the PDF, a link to a name is an internal link (a destination), a link
to the documentation or to another page an address.  In the web page,
Typst 0.15's HTML export writes a labelled place as an element with an
`id` of its own (`id="loc-3"`, not the label's name) and a link to it as
`href="#loc-3"`; links to addresses are `<a href>`.  Labels are therefore
good within a page, not as addresses from other pages.

### The legend

At the end of the text, a small legend recalls the look of the roles:
the words variable, hypothesis, claim, fact and justification, each in the look of its
role, and, for a text checked by cyp, the status marks with their
meanings (✔ proved, ✘ not proved, ◆ left to a Proof block, ▫ nothing to
check).  Its words are in the language of the text: the uses
`legend-var`, ..., `legend-none` of the lexicon, in its ten languages
(`write-word`).  In the web page it is a `footer class="legend"`, and each
role in it is a switch (a check box) that turns the colour of that role on
and off in the whole text (CSS only, no script).

The roles coloured are all of them by default; `pdf.sh --roles claim,by`
(Typst's `--input roles=...`) colours only those listed: the others look
like plain formulas, the PDF's legend lists only the coloured roles, and
the web page starts with only their switches on.

### The gallery

`sh prooftext/gallery.sh OUT` makes the web page and the PDF of each text
of the repository, and an index (the published gallery,
https://thery.github.io/coq_tmp/txt/).  It first writes the Typst source
of every text, then compiles each page with its links, given on the
command line (`pdf.sh --links`, Typst's `--input links=...`, the
template's `page-links`), above the text: the index, the same text in the
other languages (by their codes, `fr`, `ar`, ...), and the same text
checked by cyp ("checked by cyp") or not checked ("not checked"), when
the gallery has them.  The same text is the same file name, without
`.checked`, in any section of the gallery; its language is the `lang`
field of its header.  A link without an extension leads to a page of the
same kind: the web page links to web pages, the PDF to PDFs (relative
addresses, which a browser's PDF viewer follows).

### Fonts

The fonts on this machine cover every script of the lexicon.  Typst warns
when a character has no font, and `typst/check.sh` treats a warning as a
failure.

| script | font |
|---|---|
| Latin, Cyrillic (en, fr, it, de, nl, la, ru) | Libertinus Serif |
| Arabic (ar) | Noto Naskh Arabic |
| Chinese (zh), Korean (ko) | Noto Serif CJK SC, Noto Serif CJK KR (variable fonts) |
| formulas as code | DejaVu Sans Mono; Noto Sans Mono CJK for Chinese or Korean characters |
| formulas as mathematics | New Computer Modern Math (Typst's own); in the HTML page Latin Modern Math |
| marks | DejaVu Sans |

Missing: a monospace font for Arabic.  An Arabic name in a formula would
be shown in a proportional font.  No formula in the texts has one.

### The HTML page

`pdf.sh --html proof.md` makes `proof.html` from the same Typst source,
with Typst's HTML export (`typst compile --features html --format html`,
experimental in Typst 0.15; `pdf.sh` hides its warning about that).  Its
maths are MathML (`<math>`), which browsers draw without JavaScript.  The
template has an HTML version of each of its functions (`on-html`): a
formula is a `span` with the classes `formula` and its role (`formula
claim`), a step an item of nested lists (`ul class="steps"`, `li
class="step"`), a status a `span class="mark ok"`, cyp's message a `div
class="message ko"`, the legend a `footer class="legend"`, the links of
a gallery a `nav class="gallery"`, and a small style sheet, made from the
template's colours, gives them their look (the mark of a role is a
border: browsers draw no text decoration under MathML).  The page needs nothing else: no
JavaScript, no file beside it.

What Typst's HTML export does not do, so that the template does it
itself:

- the layout of the PDF (grids, padding, the page): ignored, with a
  warning each time; hence the lists and the style sheet;
- the colours of text (`text(fill: ...)`), highlights, underlines and
  boxes: dropped; hence the classes;
- labels: kept, but as ids of Typst's own (`loc-N`), see "Links";
- the style sheet goes in the body (`html.elem("style")`), as Typst gives
  no way to add to the `head`; browsers accept it;
- Chrome draws Typst's stretchy parentheses `(x)` with wide gaps; the
  writer therefore writes parentheses that keep their size, `\(x\)`, but
  around a fraction (the same in the PDF).

The page was looked at in Chrome (headless screenshots) for a text of
xtext, a checked text with its statuses and messages, and the unit tests
of the printer; with the links and the new look of the roles, for
`drinker`, `or_commut` in French and the pages of a small gallery.  Firefox was not tried.

### Tests

`sh prooftext/typst/check.sh` (about 80 s, with cyp built; needs `qpdf`):

1. for the ten texts that xtext writes in Typst (`xtext/examples-typst/`:
   five in English, one each in French, Arabic, Chinese, Russian and
   Korean), the Typst source read back from their Markdown text
   (`xtext/examples/`) is the same, character for character;
2. for two texts checked by cyp (`xtext/cyp-check/add_0_r.checked.md`,
   all proved, and `half_le.checked.md`, with steps not proved and cyp's
   messages; their `flags` line left out), the Typst source is the
   expected one (`typst/tests/*.typ`);
3. the formulas as mathematics: the unit tests of the printer
   (`check_maths.v`, 53 formulas and declarations), and ten texts (from
   the standard library, the theses, the reals, and cyp's `square_pos`):
   none of their formulas is left as code;
4. the formulas as code (`--code`): all of them are code;
5. every Typst source of 1-4 compiles to a PDF, without errors or
   warnings (the PDFs are in `typst/tests/out/`);
6. the HTML pages of `half_le.checked` and of the unit tests compile;
   they have MathML and the classes of the roles and statuses;
7. the round, when cyp is built: xtext's `or_commut` checked by cyp, then
   the PDF of the checked text; cyp's `sqrt_square` (real numbers)
   checked, then its PDF and its HTML page;
8. the links, on a small gallery of four pages built in
   `typst/tests/out/gallery` (`ABCD` and `or_commut` in English,
   `or_commut` in French and checked by cyp): the names of `ABCD` link
   to their steps (every `href="#loc-N"` of the page has its `id`, the
   PDF has destinations), a justification and a lemma of the text link
   to their documentation, each page links to the index, to the same
   text in French and checked by cyp, and back (in the HTML and in the
   PDF), and the page has its legend.

`check.v` tests the reader (places, a text read and written back), the
marks of a checked step, the parts of a text and the Typst strings, and
the links: the labels of the names, their uses in the text, after a
fact and in a justification, a name out of its scope and a word of the
lexicon (not linked), the documentation of a lemma of the corelib and of
the stdlib (`Nat.lt_eq_cases`), a tactic (no link), and the legend in
English and French.

### Limits

- A formula without a class (cyp's own examples write few classes) is
  shown without a role.  The Typst writer does not guess roles from the
  words, as cyp does (`cyp/vernac/elpi/text.elpi`, not shared).  The texts
  of xtext have a class on every formula.
- In an Arabic text, a run of Latin words (`or (or_intror),`) is ordered
  by the Unicode bidirectional algorithm, as a Markdown viewer would order
  it.
- Markdown beyond the format (bold, links, code blocks) is shown as plain
  text.
- The PDFs were checked by looking at rendered pages: English, French,
  Arabic, Chinese, Russian and Korean texts, two checked texts, and the
  texts in mathematics of the tests.  No reader of these languages has
  reviewed them.
- Links: a name is a word between spaces and ASCII punctuation; in a
  text written without spaces (Chinese by hand, "由h4得") a name glued to
  its neighbours is not found (xtext puts spaces around names in every
  language).  A word of the lexicon is never a name, even when it is one
  (`and` in "the definition of and" is not linked to `Logic.and`); a word
  of a text written by hand that is not in the lexicon and is the name of
  a constant of the corelib or the stdlib (`not`, `pred`) is linked.  A
  lemma known only by a short name that the `require` line does not
  import (`subrelation_proper` in `Nat.le_trans`) is not linked.
- A formula wider than its line is a box of its own lines in the PDF (a
  box, unlike a highlight, does not break inside a paragraph).

## Formulas as mathematics

A formula of a proof text is a Rocq string, `forall n : nat, n + 0 = n`.
For the PDF and the HTML page it is shown as mathematics, ∀ n ∈ ℕ, n + 0
= n, in three steps, each in its own file:

1. **Elaboration** (`maths.elpi`): the command `Typst` runs in Rocq, after
   the `require` line of the text; it elaborates each formula to a term
   (`coq.parse.argument`), in the notation scope of the header (`scope`).
   The variables a formula uses are those declared before it: each `Let`
   (a formula of class `var`, `a b : Z` or `u := e`, or a formula without
   a class that has the form of a declaration) puts its variables in the
   context of the formulas after it, in the statement and in the steps.
   As in cyp, a declaration in a step holds in its sub-steps and in the
   steps after it in its list.  This is simpler than cyp's elaboration,
   which builds the proof: the hypotheses are not needed to elaborate a
   formula, only the variables.
2. **Printing** (`maths.elpi`): the term is printed as a formula tree (a
   `mexp`: numbers, variables, texts, symbols, operators, rows,
   parentheses, fractions, powers, roots, delimiters, function
   applications), which says what the formula is, not how a target
   writes it.  A constant is printed as its entry of the table says;
   without an entry, as a function of its explicit arguments, f(x, y)
   (its implicit ones left out), or its name alone, upright.  A
   variable is in italics, a letter followed by digits with a subscript
   (n0: n₀).  A dependent product is ∀, grouped while the type is the
   same (∀ m, n ∈ ℕ); a variable is bound by ∈ when its type is a type
   of elements (ℕ, ℝ, list ℕ) and by : otherwise (a proposition, a
   function type); a non-dependent product is →, fun x => b is x ↦ b.
   Numbers are what Rocq prints as numbers (2, -1, 1.5, of any type).
   Parentheses come from the levels: an operand is in parentheses when
   its level is above what its place allows (on the side of the
   associativity, the operator's level; else one less), and a sign right
   after an arithmetic operator too, a - (-b).  A term that none of this
   covers (a match, a let, a fix) is Rocq's own text, upright, in
   parentheses when it is an operand.
3. **Writing** (`maths-typst.elpi`): the tree as Typst maths code, `$...$`,
   which Typst typesets in the PDF and turns into MathML in the HTML page.
   A symbol is written as it is (≤, ℕ, +), a word or two ASCII characters
   as a text with the class of the operator (`class("binary", "mod")`), a
   fraction `frac(a, b)`, a power `a^(b)`, a root `sqrt(a)`, delimiters
   `lr(| a |)`.  Another target (MathML, LaTeX) needs only another writer
   of the same tree.

A formula that does not elaborate keeps its text, shown as code.  On the
79 texts of xtext and the 8 of cyp's examples (2090 formulas), 2 formulas
are shown as code (`n` and `l1`, bound by a `fix` that no `Let`
declares), and 1 has a part in Rocq's text (a `match`).

### The table

`maths-table.elpi` has one entry per constant, `maths-notation Name
Form`, with a comment.  `Name` is a suffix of the constant's full name
(`"Rplus"`, `"Z.le"`, `"Logic.eq"`): the longest suffix with an entry
wins, so `"Z.le"` is found before a `"le"` would be.  The forms say what
the notation is, not how a target writes it:

| form | meaning | examples |
|---|---|---|
| `binary S L Assoc` | a S b, level L, `left-assoc`, `right-assoc`, `no-assoc` | `Rplus` +, `Datatypes.app` ++, `Z.modulo` mod |
| `conjunction S L` | A S B, and a chain a < b < c for two relations on the same middle term | `Logic.and` ∧ |
| `relation S Neg L` | a S b; ¬ (a S b) is a Neg b when Neg is not "" | `Logic.eq` = ≠, `Rle` ≤, `List.In` ∈ ∉ |
| `unary S L`, `negation S L`, `sign S L` | S a; a negation takes a relation's negated symbol; a sign is in parentheses after an arithmetic operator | `Datatypes.negb` ¬, `Logic.not` ¬, `Ropp` - |
| `fraction`, `reciprocal` | a over b, 1 over a | `Rdiv`, `Rinv` |
| `power`, `fixed-power N` | a to the power b, or N | `Rpow_def.pow`, `Z.pow`, `Rsqr` (²) |
| `root` | √a | `R_sqrt.sqrt` |
| `enclosed L R` | a between two delimiters | `Rabs`, `Z.abs` \| \| |
| `glyph S` | a symbol for a constant without operands | `Datatypes.nat` ℕ, `BinNums.Z` ℤ, `RbaseSymbolsImpl.R` ℝ, `Logic.True` ⊤ |
| `function F` | F(a, b), F upright | `Rtrigo_def.exp` exp, `Rmax` max |
| `hidden` | a coercion, shown as its operand | `INR`, `IZR`, `Z.of_nat` |
| `binder S` | a quantifier on a function, S x ∈ A, P | `Logic.ex` ∃ |

The table covers the logic (∧ ∨ ¬ ↔ ⊤ ⊥ = ∃), the orders and arithmetic
of `nat`, `N`, `Z`, `R` and `Q` (+ - ⋅ div mod, powers, fractions,
|·|, √, exp, ln, sin, cos, max, min, the coercions between numbers),
booleans (written ∧ ∨ ¬), lists (:: ++ [] ∈) and the types ℕ ℤ ℚ ℝ 𝔹
and pairs ×.  The levels are those of Rocq's notations for the same
symbols (`negb`, written ¬, has ¬'s level).

To add entries, a library accumulates clauses to the command `Typst`, as
cyp's rules are added; no code changes.  A file `MyNotations.v`:

```coq
From Stdlib Require Import Reals.
From ProofText Require Import Typst.
Elpi Accumulate Typst lp:{{
  prooftext.maths-notation "Rtrigo1.tan" (prooftext.function "tan").
  prooftext.maths-notation "R_Ifp.Int_part" (prooftext.enclosed "⌊" "⌋").
}}.
```

and a text whose header requires it, `require: From Stdlib Require Import
Reals. Open Scope R_scope. From My Require Import MyNotations.` (with
`pdf.sh --flags "-R dir My"`, or a `flags` line), shows `tan x` as tan(x)
and `IZR (Int_part x)` as ⌊x⌋.  An entry with a longer suffix overrides a
shorter one; `:before` puts a clause before those of the table.

### Limits of the mathematics

- The elaboration knows only the variables of the `Let`s: a formula that
  names a variable bound otherwise (by a `fix`, as in xtext's texts of
  structural recursion) is shown as code.
- A notation of Rocq that is not a constant (a `match`, a record, a
  `let`) is shown as Rocq's text; so are the constants without an entry
  that are not applied (`S` is S(m), not m + 1, by design).
- A coercion is hidden, so `INR n + 1 = INR (n + 1)` reads n + 1 = n + 1;
  `Rsqr x` and `x ^ 2` both read x².
- Binders keep their names: a binder that shadows a variable of the
  context is not renamed.
- The entries a library adds go to one command: `Typst` (the PDFs and
  pages of `pdf.sh`); xtext's `Explain foo to "foo.typ"` has its own
  program, where they are added the same way (`Elpi Accumulate Explain`).
- In a PDF, a word operator (div, mod) inside a highlighted formula has
  its own highlight box; inline fractions are small (Typst's inline
  maths).
