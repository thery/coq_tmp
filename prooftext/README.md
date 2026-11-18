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
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "names.elpi" as pt_names.
From ProofText Extra Dependency "tactics.elpi" as pt_tactics.
From ProofText Extra Dependency "checked.elpi" as pt_checked.
From ProofText Extra Dependency "typst.elpi" as pt_typst.
Elpi Accumulate File lex_core pt_header pt_document pt_formulas pt_names pt_tactics
  pt_checked pt_typst.
```

with `-Q prooftext ProofText` and `-Q lexicon Lexicon`.  `lexicon.elpi`
comes first (`formulas.elpi` uses its roles), `header.elpi` before
`document.elpi`, `document.elpi` before `checked.elpi`, and `typst.elpi`
last.  A tool loads only the files it uses.  Every name is in the namespace `prooftext`
(`prooftext.write-document`, `prooftext.step`, ...), so that it does not
meet the names of the tools.

Tests: `rocq c -Q ../lexicon Lexicon -Q . ProofText check.v`; those of the
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

  and the writing of a header: `header-lines Fields Lines` (a key that
  is not a `header-key` is an error), `lang-fields Lang Fields` (no field
  for the default language), `by-field Tactics Field`;
- `document.elpi`: the document tree, `document Fields Name Place
  Statement Steps`, a step `step Place Text Sub-steps`, a `place` (`lines
  First Last`, the lines of a text in its file, numbered from 0, given by
  a reader; `unplaced` for a text being written), the writer
  `write-document D Text`, and a reader, `read-document File D` (the
  reader's contract below; cyp keeps its own reader);
- `checked.elpi`: what a checker adds to the text of a step (cyp's
  `.checked.md`): `status-mark Status Mark` (`ok` ✅, `ko` ❌, `todo` 🔶,
  `none` ▫️, cyp's names of the statuses), `message-block M S` (the
  folded block `<details><summary>M</summary></details>` under a step),
  `conditions-mark Ids S` (`**[2a, 2b]**`, the conditions left to a Proof
  block), and their reading, `split-checked Text (checked Status
  Conditions Message) Rest`.  cyp writes its marks with these predicates;
- `typst.elpi`: the Typst writer, `write-typst D Text`, and `write-as File
  D Text` (Typst for a file `.typ`, Markdown otherwise); see "The PDF of a
  proof text";
- `formulas.elpi`: `role-tag Role Tag` (`rvar` `var`, `rhyp` `hyp`,
  `rclaim` `claim`, `rfact` `fact`, and `rback`, a claim that replaces
  the goal, written as a claim: read back, the class `claim` gives
  `rclaim`, the first role with it), `formula Role F S` (`` `F`{.tag} ``),
  `justification J S` (`*by J*`), `is-justification S`, and the reading
  of a step's justification, `split-justification S J Rest`;
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
`document`, with places (`read-document` in `document.elpi`; cyp's reader
is `cyp/vernac/elpi/markdown.elpi`, the predicate is the reader's):

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
- within the text of a statement or a step, formulas and their roles,
  hypothesis names `(h)` and the justification are read as in
  `formulas.elpi`, with the phrases of the lexicon for the formulas that
  have no class (cyp: `cyp/vernac/elpi/text.elpi`).

What a document written by `write-document` gives when read back is the
same document, with places.

## The PDF of a proof text (Typst)

```sh
prooftext/pdf.sh xtext/examples/or_commut.md          # or_commut.typ, then or_commut.pdf
prooftext/pdf.sh xtext/cyp-check/half_le.checked.md   # a text checked by cyp, with its statuses
prooftext/pdf.sh foo.typ                              # a text xtext wrote in Typst
```

`pdf.sh` writes the Typst source of each text next to it (`proof.md` gives
`proof.typ`), then its PDF with [Typst](https://typst.app) (0.15).  It
needs the opam switch `elpi4` and `typst`; it compiles `Typst.vo` when it
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

#statement[#"Let "#var("A B : Prop")#". Assume "#hyp("A /\\ B")#" "#name("H")#". We prove "#claim("B /\\ A")#"."]

#steps((
  step("1", [#"Going back to the definition of and (match) in "#fact("A /\\ B")#" "#name("H")#", we prove "#claim("B /\\ A")#":"], (
    step("1.1", [#"Assume "#hyp("A")#" "#name("a")#" and "#hyp("B")#" "#name("b")#"."], (
      step("1.1.1", [... #claim("B /\\ A")#" "#by("Corelib.Init.Logic.conj")#"."], ()),
    )),
  )),
))
```

The text of a statement or of a step is cut into its parts: the formulas
with their roles, the name `(h)` given to a formula (right after it), the
justification `*by X*`, and the plain text between them.  Each part is
written as a Typst string, so that no character of the text is read as
Typst markup.

### What the PDF shows

- **The header** is a small title block: the name of the theorem, then
  each field of the header (`require`, `flags`, `by`, `lang`, ...) with
  its value as code.
- **Formulas** are Rocq code, shown in a monospace font.  They are not
  turned into mathematical notation: Rocq notations have no clean, generic
  translation.  Each role has its own style, the same in every text:

  | role | class | style |
  |---|---|---|
  | variable | `{.var}` | blue |
  | hypothesis | `{.hyp}` | amber, on a light amber background |
  | claim | `{.claim}` | green, on a light green background |
  | fact (a mention) | `{.fact}` | purple, with a dotted underline |
  | no class | | dark grey |

  The name `(h)` of a formula is amber.  The justification is grey,
  *by* `X`.
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

### Fonts

The fonts on this machine cover every script of the lexicon.  Typst warns
when a character has no font, and `typst/check.sh` treats a warning as a
failure.

| script | font |
|---|---|
| Latin, Cyrillic (en, fr, it, de, nl, la, ru) | Libertinus Serif |
| Arabic (ar) | Noto Naskh Arabic |
| Chinese (zh), Korean (ko) | Noto Serif CJK SC, Noto Serif CJK KR (variable fonts) |
| formulas | DejaVu Sans Mono; Noto Sans Mono CJK for Chinese or Korean characters |
| marks | DejaVu Sans |

Missing: a monospace font for Arabic.  An Arabic name in a formula would
be shown in a proportional font.  No formula in the texts has one.

### Tests

`sh prooftext/typst/check.sh` (about 15 s):

1. for the ten texts that xtext writes in Typst (`xtext/examples-typst/`:
   five in English, one each in French, Arabic, Chinese, Russian and
   Korean), the Typst source read back from their Markdown text
   (`xtext/examples/`) is the same, character for character;
2. for two texts checked by cyp (`xtext/cyp-check/add_0_r.checked.md`,
   all proved, and `half_le.checked.md`, with steps not proved and cyp's
   messages), the Typst source is the expected one (`typst/tests/*.typ`);
3. every Typst source of 1 and 2 compiles to a PDF, without errors or
   warnings (the PDFs are in `typst/tests/out/`);
4. the round, when cyp is built: xtext's `or_commut` checked by cyp, then
   the PDF of the checked text.

`check.v` tests the reader (places, a text read and written back), the
marks of a checked step, the parts of a text and the Typst strings.

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
  Arabic, Chinese, Russian and Korean texts, and two checked texts.  No
  reader of these languages has reviewed them.
