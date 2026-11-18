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
Elpi Accumulate File lex_core pt_header pt_document pt_formulas pt_names pt_tactics.
```

with `-Q prooftext ProofText` and `-Q lexicon Lexicon`.  `lexicon.elpi`
comes first (`formulas.elpi` uses its roles), `header.elpi` before
`document.elpi`.  Every name is in the namespace `prooftext`
(`prooftext.write-document`, `prooftext.step`, ...), so that it does not
meet the names of the tools.

Tests: `rocq c -Q ../lexicon Lexicon -Q . ProofText check.v`.

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
  a reader; `unplaced` for a text being written), and the writer
  `write-document D Text`;
- `formulas.elpi`: `role-tag Role Tag` (`rvar` `var`, `rhyp` `hyp`,
  `rclaim` `claim`, `rfact` `fact`, and `rback`, a claim that replaces
  the goal, written as a claim: read back, the class `claim` gives
  `rclaim`, the first role with it), `formula Role F S` (`` `F`{.tag} ``),
  `justification J S` (`*by J*`), `is-justification S`;
- `names.elpi`: `fresh-name Used Wanted Name`, `Wanted` if it is not in
  use, else `Wanted0`, `Wanted1`, ...: the names a text introduces must
  differ from the names in use, so that `*by h*` names one hypothesis
  (xtext names its binders with it, `binder-name` in
  `xtext/elpi/printing.elpi`; cyp can name its hypotheses with it);
- `tactics.elpi`: `tactic Name`, the tactics a text may name in `*by X*`
  or in its `by` field, and `unknown-tactics Names Unknown`.  Each tool
  runs a name its own way: cyp maps it to an Ltac definition
  (`tactic-name Name Ltac`, `cyp/vernac/Cyp.v`); xtext writes only these
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
`document`, with places (cyp's reader is `cyp/vernac/elpi/markdown.elpi`;
the predicate is the reader's):

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
