# prooftext: the format of proof texts

A *proof text* is a proof written as a Markdown file, with its formulas in
Rocq syntax.  Two tools share the format: [xtext](../xtext/README.md)
writes proof texts from Rocq proofs, [cyp](../cyp/README.md) reads them and
checks them step by step.  This library holds what the two must agree on,
so that each tool does not keep its own copy: the reader of a text into
the tree of its nodes, the document of a writer and its writing, the
header and its fields, how a formula carries its role, how a node names
its justifications, fresh names, and the tactics a text may name.  The words of the texts (the phrases of each language) are in the
[lexicon](../lexicon/README.md).

## Loading

```coq
From Lexicon Extra Dependency "lexicon.elpi" as lex_core.
From Lexicon Extra Dependency "lang_en.elpi" as lex_en.   (* and the other tables *)
From ProofText Extra Dependency "header.elpi" as pt_header.
From ProofText Extra Dependency "document.elpi" as pt_document.
From ProofText Extra Dependency "formulas.elpi" as pt_formulas.
From ProofText Extra Dependency "tree.elpi" as pt_tree.
From ProofText Extra Dependency "nodes.elpi" as pt_nodes.
From ProofText Extra Dependency "names.elpi" as pt_names.
From ProofText Extra Dependency "tactics.elpi" as pt_tactics.
From ProofText Extra Dependency "checked.elpi" as pt_checked.
From ProofText Extra Dependency "maths-table.elpi" as pt_maths_table.
From ProofText Extra Dependency "maths.elpi" as pt_maths.
From ProofText Extra Dependency "maths-typst.elpi" as pt_maths_typst.
From ProofText Extra Dependency "links.elpi" as pt_links.
From ProofText Extra Dependency "typst.elpi" as pt_typst.
Elpi Accumulate File lex_core lex_en pt_header pt_document pt_formulas pt_tree pt_nodes pt_names pt_tactics
  pt_checked pt_maths_table pt_maths pt_maths_typst pt_links pt_typst.
```

with `-Q prooftext ProofText` and `-Q lexicon Lexicon`.  `lexicon.elpi`
comes first (`formulas.elpi` uses its roles), `header.elpi` before
`document.elpi`, `document.elpi` before `formulas.elpi`, `tree.elpi`
(the reader) and `nodes.elpi` (what its nodes say) in this order, and
before `checked.elpi`, the table of
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

A proof text is the tree of the 2003 paper (§2.2, its tags `p`, `c`, `h`,
`v`, `n`, `f`, `j`), written in Markdown.  Its proposal, with the paper's
examples in both syntaxes, is [../proposal/PROPOSAL.md](../proposal/PROPOSAL.md).

```markdown
---
require: From Stdlib Require Import Arith.
---

# praeclarum

Let `x y z t : Prop`{.var}. If `x -> z`{.hyp} and `y -> t`{.hyp} then `(x /\ y) -> (z /\ t)`{.claim}.

- Suppose `x /\ y`{.hyp}.
  - We get `z`{.claim} by `x -> z`{.fact}, since
    - we have `x`{.claim}.
  - We get `t`{.claim} by `y -> t`{.fact}, since
    - we have `y`{.claim}.

  Altogether we have `z /\ t`{.claim}.
```

- the **header**, between two lines `---`, one field `key: value` per line;
- the **title**, `# name`, the name of the theorem;
- everything after the title is the **top node**: the statement and its
  proof.

**The tree.**  A node (the paper's `<p>`) has, in its own text:

| tag (paper) | Markdown | in a node |
|---|---|---|
| conclusion `<c>` | `` `C`{.claim} ``, or `` `C`{.goal} `` for an open goal | exactly one |
| name `<n>` of the node | `(n)` right after its conclusion | at most one; the name later nodes use (else `c` and its number, `c2_1` for node 2.1) |
| variable `<v>` | `` `x y : T`{.var} ``, `` `u := e`{.var} `` | any; they hold in the node and its subnodes |
| hypothesis `<h>` | `` `A`{.hyp} (h) `` | any, each with at most one name; they hold in the node and its subnodes |
| fact `<f>` | `` `F`{.fact} `` | any: formulas the node uses, each a hypothesis or a conclusion it can see |
| justification `<j>` | `*X*{.just}` | any: names of hypotheses, nodes, lemmas, rules or tactics, the two fixed methods `match` and `induction`, the inductive type they eliminate |

and its **subnodes**, in the order of the text.  The parts may come in any
order: the conclusion first ("We prove C: ...") or last ("..., so we get
C").  A formula with no class, and any emphasis without `{.just}`, are
plain text: shown, without colour, and not used.  The word "by" is an
ordinary word.

**Open goals.**  A proof in progress has steps that its author has not
proved yet: their conclusion is tagged `` `G`{.goal} `` instead of
`` `G`{.claim} `` ("Prove `z`{.goal}.", as xtext's `ExtractText_partial`
writes the open goals of a proof).  It is the conclusion of its node in
every respect (its name, its scope, the nodes after it use it), but a
checker does not try it: cyp leaves it as a goal of the Proof block.  The
PDF and the web page frame it (see "What the PDF shows").

**Fixed justifications.**  Two names are methods, the same in every
language, that say how a step eliminates an object:

| justification | meaning | example |
|---|---|---|
| `*match*{.just}` | a case analysis on the hypotheses or variables the node names (one case per constructor, no induction hypotheses) | "Going back to the definition of *and*{.just} (*match*{.just}) in *H0*{.just}" |
| `*induction*{.just}` | an induction on the variables or hypotheses the node names | "By induction on *n*{.just} (*nat*{.just}, *induction*{.just})" |

The name of an inductive type, `*and*{.just}`, may come with them: it
says the type of the object eliminated (with no object named, the one
object of that type in scope); alone, it justifies nothing.  The cases
are the subnodes, as for any other step.  `match` is a keyword of Rocq,
never a name; `induction` may be the name of a lemma or of a hypothesis
in Rocq, but as a justification it always means the method (such a lemma
is named by a qualified name).  A non-standard elimination principle
(`*two_step*{.just}`, `*strong_induction*{.just}`) is a lemma, named as
such.  The list is `method` in `tactics.elpi`.

**Two syntaxes for the same tree**, which may be mixed at any depth:

- *structured*: a list item is a node; its sub-items are its subnodes;
  the text of the item up to its first sub-item, and the paragraphs
  indented under the item after its sub-items (the *closing paragraph*,
  "Altogether we have ..." above), are its own text;
- *free*: a span `[ ... ]{.p}` inside a paragraph is a node; spans nest.
  A node of several paragraphs is a div, the lines between `::: p` and
  `:::`.  The marks `[`, `]{.p}`, `:::` are not shown in the PDF and the
  web page.

A part of the text belongs to the innermost node opened around it (by an
item, a span or a div).  The same proof, free:

```markdown
[Suppose `x /\ y`{.hyp}. [[We have `x`{.claim}]{.p}, so by `x -> z`{.fact}
we get `z`{.claim}.]{.p} [[We have `y`{.claim}]{.p}, so by `y -> t`{.fact}
we get `t`{.claim}.]{.p} Altogether we have `z /\ t`{.claim}.]{.p}
```

and mixed, a list item holding a span: `- [We have `x`{.claim}]{.p}, so
by `x -> z`{.fact} we get `z`{.claim}.` is one node (conclusion `z`) with
one subnode (conclusion `x`).

**Remarks.**  An item, a span or a div whose own text has no tag at all
is a *remark*: it is shown, it is no node of the proof, and its subnodes
(if any) are subnodes of the node around it.

**Scope, and what a node proves.**  For a node P with variables V,
hypotheses H, conclusion C and subnodes P1 ... Pk:

- V and H hold in P and in its subnodes, nowhere else;
- seen from outside (from the node around it, and from the nodes after it
  in its list), P is the formula ∀ V, H → C;
- what a checker proves for P is C, in the context of the variables and
  hypotheses of P and of the nodes around it, of P1 ... Pk seen from
  outside, and of the nodes before P in its list and before each node
  around it, seen from outside (the paper's rule, end of §2.3: "the
  conclusion of p_i is visible inside p_j for i < j").  The justifications
  and the facts of P say how (cyp: [../cyp/README.md](../cyp/README.md)).

The top node is the statement with its proof: its variables, hypotheses
and conclusion are those of the theorem, its subnodes the steps of the
proof.  There are no backward words any more ("it suffices to prove"):
going backwards is nesting, the conclusion of a node follows from its
subnodes.

**Errors** of the tree, each at its node and its line (`tree-errors`,
`nodes.elpi`; cyp reports them):

| error | example |
|---|---|
| a node with no conclusion (it has tags, but no `{.claim}`) | `- Assume `x`{.hyp} (k).` with sub-items and no closing paragraph |
| a node with two conclusions | `we have `A`{.claim}, hence `B`{.claim}` in one node |
| a statement with no conclusion | no `{.claim}` after the title, outside every node |
| a name out of scope | `*k*{.just}` outside the node that assumes `k` |
| a name given twice in one scope | two hypotheses `(h)` both visible |
| an unknown class | `` `F`{.clam} ``, `*h*{.jsut}`, `]{.q}`, `::: q` |
| a justification that is not a name | `*by lia*{.just}` |
| an unclosed div, a span or div closed but not opened | `::: p` with no `:::`, `]{.p}` with no `[` before it |

Two errors need the meaning of the names, and are the checker's: a
justification that names nothing known (no hypothesis, node, lemma, rule
or tactic), and a fact that is no hypothesis or conclusion in scope.

**Departures from the 2003 paper.**

- A node may have several justifications, each one name, written where
  the sentence mentions it ("Applying *i*{.just} to *k*{.just}"): the paper
  has at most one `<j>` per `<p>`, which may hold several names.
- Two syntaxes for one tree (the paper has the tags only), and the
  closing paragraph of a list item.
- Remarks: a text with no tag is shown and not checked.

**The transition.**  The texts written before the tree (xtext writes the
tree now) name their justification `*by X*`, after the sentence: it is
still read as the justification X (`by-part`).  Its other
departures from the tree are errors (a scope with no conclusion, a fact
that names no formula in scope).

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
- `document.elpi`: the document of a writer, `document Fields Name Place
  Statement Steps`, a step `step Place Text Sub-steps`, or `closed-step
  Place Text Sub-steps Closing` with its closing paragraph, a `place` (`lines
  First Last`, the lines of a text in its file, numbered from 0, given by
  a reader; `unplaced` for a text being written), the writer
  `write-document D Text` (and `write-document-as Markup D Text`, the
  markup `tagged` or `untagged`: plain text), and the number of a step, `step-number Parent
  K Number` (Dewey notation, `2.1` the first sub-step of step 2: cyp
  numbers its nodes with it, the Typst writer its steps);
- `tree.elpi`: the reader, `read-tree File T` and `lines-tree Lines T`,
  into the tree of nodes (below, the reader's contract);
- `nodes.elpi`: what the nodes of a tree say, their numbers, and the
  errors of a tree, `tree-errors` (below, the reader's contract);
- `checked.elpi`: what a checker adds to the text of a step (cyp's
  `.checked.md`): `status-mark Status Mark` (`ok` ✅, `ko` ❌, `todo` 🔶,
  `none` ▫️, cyp's names of the statuses), `message-block M S` (the
  folded block `<details><summary>M</summary></details>` under a step),
  `conditions-mark Ids S` (`**[2.1]**`, the condition left to a Proof
  block), and their reading, `split-checked Text (checked Status
  Conditions Message) Rest`.  cyp writes its marks with these predicates;
- `typst.elpi`: the Typst writer, `write-typst-tree Style T Text` (the
  tree of a text, formulas in the style `maths` or `code`; it needs
  `tree.elpi` and `nodes.elpi`), `write-typst D Text` (a document, through
  its Markdown; formulas in mathematics), `write-typst-in Style D Text`, and
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
  `rclaim` `claim`, `rgoal` `goal` (an open goal), `rfact` `fact`, and `rback`, a backward claim of the
  lexicon, which the format no longer has, written as a claim: read back,
  the class `claim` gives `rclaim`, the first role with it),
  `justification-class C` (`just`), `formula Role F S` (`` `F`{.tag} ``),
  `justification-name J S` (`*J*{.just}`), `untagged-formula F S` (`` `F` ``, plain text),
  `justification J S` (`*by J*`, the form of the texts written before the
  tree, read still),
  `is-justification S`, `is-name S`, and the reading of the text of a
  node, `text-parts Text Parts` (below, the reader's contract);
- `names.elpi`: `fresh-name Used Wanted Name`, `Wanted` if it is not in
  use, else `Wanted0`, `Wanted1`, ...: the names a text introduces must
  differ from the names in use, so that `*by h*` names one hypothesis
  (xtext names its binders with it, `binder-name` in
  `xtext/elpi/printing.elpi`; cyp can name its hypotheses with it);
- `tactics.elpi`: `tactic Name`, the tactics a text may name in a justification
  or in its `by` field, and `unknown-tactics Names Unknown`; `method
  Name`, the two fixed justifications `match` and `induction` (no
  tactics: a `by` field does not name them).  Each tool
  runs a name its own way: in cyp each is a word declared by
  `CypJustification "Name" := word_Name.` (`cyp/vernac/Cyp.v`; `word_Name`
  is the Ltac of `prooftext/Tactics.v` that xtext runs too; a proof
  declares its own words the same way); xtext writes only these
  names (the text of its tactics, `xtext-tactic Ltac Name` and
  `xtext-guard-tactic Ltac Name` in `xtext/ExtractText.v`, which run them as
  cyp does, with no time limit), and `xtext/vocab_check.v` checks it.  A name added to one
  tool's table goes here first.

## Writing a proof text

`write-document (document Fields Name _ Statement Steps) Text` gives the
header lines, an empty line, `# Name`, an empty line, the statement on one
line, an empty line, then one line per step, `- Text`, the sub-steps of a
step below it with two more spaces of indentation, and the closing
paragraph of a `closed-step` after its sub-steps, after an empty line,
indented as the text of its step; `Text` ends with a newline.  The places
are not used.  A writer gives each step its text in one line; xtext also
ends each with a punctuation mark.

`write-document-as untagged D Text` writes the same lines as plain text,
for a reader (the text xtext prints): no header and no title, each
formula without its backticks and its class, each justification without
its emphasis (`plain-text`, formulas.elpi); `write-document D Text` is
`write-document-as tagged D Text`.

## Reading a proof text (the reader's contract)

`read-tree File T` (`tree.elpi`) gives `proof-text Fields Name Top`, the
fields of the header, the name, and the top node, from the lines of the
file (numbered from 0); `lines-tree Lines T` does it from the lines.  It
is the one reader of cyp and of the Typst back end.

- **header**: if the first line is `---` (spaces around it ignored), the
  lines up to the next line `---` are fields; a field line is `key:
  value`, spaces before the key and around the value ignored.  The keys
  that have a meaning are the `header-key`s; a reader ignores the others
  (`unknown-header-keys Lines Keys` gives them: cyp names each in a
  warning).
  Without a first line `---`, the header is empty;
- **title**: the first line after the header that starts with `# `; the
  rest of the line, trimmed, is the name;
- **the top node**: all the lines after the title;
- **blocks**: the text of a node is a sequence of blocks, separated by
  empty lines or not:
  - a *list item* is a line that starts, after spaces, with `- ` or `* `;
    it is a node, whose text is the rest of the line, the lines after it
    up to an empty line, an item or a fence (continuation lines), and then
    every block indented more than its `-` (its sub-items, and its closing
    paragraphs);
  - a *div* starts with a line `::: p` (or `::: {.p}`) and ends with the
    next line `:::` of its level; it is a node, whose text is the blocks
    between them;
  - a *paragraph* is any other line and the lines after it up to an empty
    line, an item or a fence; its lines are trimmed and joined by one
    space;
  - a block less indented than the item it would belong to ends that
    item;
- **spans**: in a paragraph, a `[` opens a span, closed by the next
  `]{.p}`; the span is a node.  The text between backticks is a formula,
  whatever it holds (a `]` there does not count); a `[` closed by a `]`
  with no class is text (`[0, 1]`), and so is a `[` that nothing closes (an
  interval `[0, 1)` in prose);
- **parts**: the own text of a node (`run`, its text and its parts) is
  read by `text-parts` (`formulas.elpi`): a **formula** is the text
  between two backticks (a backtick with no other after it is text);
  right after it may come its **class**, `{.tag}` (letters), then, after
  any number of spaces, the **name** given to it, `(h)` (an identifier);
  an emphasised text followed by a class, `*X*{.tag}`, is a **tagged
  name**, a justification for the class `just`; `*by X*` is the
  justification X of the texts written before the tree.  A part is `plain
  Words`, `formula-part Class Formula Name` (`Name` is `some h` or
  `none`), `tagged-name Class X` or `by-part X` (and `term-part Class Term
  Name`, a formula given as a Rocq term, for cyp's `Cyp Lemma`).  A name
  after a hypothesis names it; after the conclusion it names the node;
  after a fact it is shown only.

A node is `node Origin Place Mark Message Contents`: how it is opened
(`whole-text`, `list-item`, `bracketed`, `fenced`), its lines (from its
opening to its end), where its own text starts (a `spot Line Column`,
where a checker writes its status mark), where a message about it goes
(after that line, at that column), and its contents in the order of the
text: `run Text Parts`, `sub Node`, `para-end` (the end of a paragraph)
and `flaw Line Error` (an error of the reader: a div left open, a span or a
div closed but not opened, an unknown class of a span or a div; a span
left open is text, see "spans" above).
`nodes.elpi` says what a node says: `node-parts`, `claim-parts` (its
conclusions, `{.claim}` or `{.goal}`, `conclusion-class`), `is-goal-node`
(its conclusion is an open goal),
`hypothesis-names`, `variable-names`, `justification-names`, `node-name`,
`is-remark`, its numbers (`numbered-subnodes`, `node-children`, which
replaces a remark by its subnodes, `all-nodes`; the top node is `0`, its
subnodes `1`, `2`, ..., the subnodes of `2` are `2.1`, ...), and the
errors, `tree-errors Top Errors`, each `node-error Number Line Error`.

**For a writer**, the Typst back end writes from the tree itself
(`write-typst-tree`, below), so that a closing paragraph comes after its
sub-items and a free text keeps its paragraphs.

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
prooftext/pdf.sh --roles claim,just proof.md # colour only the claims and justifications (all by default)
sh prooftext/gallery.sh ~/gallery                      # every text of the repository, with an index
prooftext/pdf.sh --doc-root MyLib=../doc/ --name-links names.txt proof.md   # links to local rocq doc pages, rules, tactics
prooftext/pdf.sh --source-root CypV=https://github.com/thery/coq_tmp/blob/main/cyp/vernac/ proof.checked.md   # cyp's declared words link to their declarations
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

- **The writer is in Elpi, here**, next to the reader:
  `write-typst-tree Style T Text` (`typst.elpi`) writes the tree of
  nodes `T` that the reader gives (`read-tree`, the reader's contract
  above), so that a text in Markdown (one that xtext wrote, a text
  checked by cyp, a text written by hand, in either syntax) is shown as
  it is written.  xtext writes a document it has just built
  (`ExtractText foo to "foo.typ"`: `write-as` chooses the writer by the
  extension of the file) with `write-typst D Text`: the document's
  Markdown (`write-document`), read back into its tree, so that both
  give the same Typst source.  Reading Markdown needs no OCaml driver:
  the command `Typst "proof.md" to "proof.typ".` (`Typst.v`) is a few
  lines, and `pdf.sh` is a shell script that runs it, then `typst`.
  pandoc is not used: its generic conversion knows neither the roles nor
  the statuses.
- **The look is in a Typst template**, `typst/local/prooftext/0.1.0/prooftext.typ`.
  It is a local Typst package, `@local/prooftext:0.1.0`, so that a Typst
  source imports it by name, wherever the source is:
  `typst compile --package-path prooftext/typst proof.typ`.  The Typst
  source only calls the template's functions; the colours, fonts and
  spacing are set in one place, the template.

A Typst source (xtext's `examples-typst/and_swap.typ`, without its two lines
of comments, its `require` line shortened):

```typst
#import "@local/prooftext:0.1.0": *
#show: proof-text.with(lang: "en", numbers: false)

#title-block("and_swap", (
  ("require", "From Stdlib Require Import Arith Lia List Bool. ..."),
  ("by", "tauto | congruence | lia | firstorder | auto"),
))

#proof([#"Let "#var($A , B : "Prop"$)#". Assume "#hyp($A ∧ B$)#" "#name("H", label: "statement:H")#". We prove "#claim($B ∧ A$)#"."], (
  steps((
    step("1", [#"Going back to the definition of "#just("and", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#and")#" ("#just("match")#") in "#just("H", target: "statement:H")#", we prove "#claim($B ∧ A$)#":"], (
      steps((
        step("1.1", [#"Assume "#hyp($A$)#" "#name("a", label: "1.1:a")#" and "#hyp($B$)#" "#name("b", label: "1.1:b")#". By definition of and ("#just("conj", url: "https://rocq-prover.org/corelib/Corelib.Init.Logic.html#conj")#"), from "#just("b", target: "1.1:b")#" and "#just("a", target: "1.1:a")#" we deduce "#claim($B ∧ A$)#"."], ()),
      )),
    )),
  )),
))

#legend((("var", "variable"), ("hyp", "hypothesis"), ("claim", "claim"), ("fact", "fact"), ("just", "justification"),))
```

`proof` is the top node: its first paragraph (the statement), then its
*blocks*, in the order of the text.  The blocks of a node are its
paragraphs (`paragraph[...]`), its lists of items (`steps((...))`, each
item a `step`: its number, its first paragraph, its own blocks: its
sub-items, its closing paragraph), its divs (`division(number, (...))`)
and cyp's messages (`message(status, text)`).  A span `[ ... ]{.p}` is a
call inside the text of a paragraph, `node(number)[...]`.  The numbers
are those of the nodes (`nodes.elpi`, the numbers of cyp's conditions:
the subnodes of a node are numbered in the order of the text, whatever
their syntax).  The same proof, free (the paper's `praeclarum`):

```typst
#proof([#"Let "#var($x , y , z , t : "Prop"$)#". If "#hyp($x → z$)#" ... then "#claim($x ∧ y → z ∧ t$)#"."], (
  paragraph[#node("1")[#"Suppose "#hyp($x ∧ y$)#". "#node("1.1")[#node("1.1.1")[#"We have "#claim($x$)]#", so by "#fact($x → z$)#" we get "#claim($z$)#"."]#" ... Altogether we have "#claim($z ∧ t$)#"."]],
))
```

The text of a paragraph is cut into its parts: the formulas with their
roles, the name `(h)` given to a formula (right after it), the
justifications `*X*{.just}` (`just`), and the plain text between them,
where the names and the lemmas are links (`named`, `cited`; see
"Links").  Each part is written as a Typst string, so that no character
of the text is read as Typst markup; a formula is Typst maths, `$...$`,
made by the printer, or, as code, a string: `#claim("B /\\ A")`.  The
form of the texts written before the tree, `*by X*`, is shown as the word
*by* followed by `just("X")`.

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
  | open goal | `{.goal}` | light yellow `#fcf6c6`, the claim's | a frame, thicker, in the text too |
  | fact (a mention) | `{.fact}` | light grey `#e3e3e3` | a dotted line under it |
  | justification | `*X*{.just}` | reddish purple `#d9a9cb` (darker) | a line under it |
  | no class | | none | none |

  The backgrounds are light tints of the Okabe-Ito palette (sky blue,
  orange, yellow; grey; reddish purple), whose colours stay apart for the common kinds
  of colour blindness; there is no red and green pair.  Orange and yellow
  look alike for red-green colour blindness: the hypothesis's tint is
  darker.  The page was checked through the
  simulations of protanopia, deuteranopia and tritanopia (Machado et al.'s
  matrices, ImageMagick's `-color-matrix`, on the PDF and on the web
  page of `drinker`): the four roles stay distinct.

  An open goal (`{.goal}`, a proof in progress) is the one formula of a
  text with a frame (1 pt in the PDF, 2 px on the web page; the claim's
  mark in the legend is 0.5 pt, 1 px), on the claim's background: it is
  a claim not proved yet, and what is left to prove is seen at once.
  The frame needs no colour, so it is the same for every kind of colour
  blindness, and it stays when the colours are off (a switch of the
  legend, `pdf.sh --roles`): only the background goes.  In the PDF a formula
  is a box (Typst's highlights and underlines do not reach the symbols of
  maths); a formula wider than its line is a box as wide as the line,
  where it breaks.

  The name `(h)` of a formula is in black, in monospace.  A
  justification `*X*{.just}` is the name X, in monospace, on its
  background; the words around it ("by", "applying ... to") are ordinary
  text, and a node with several justifications has each name coloured
  where it is written.  The links are blue (Okabe-Ito blue, `#0072b2`): a
  name and a lemma that link somewhere (see "Links").
- **A structured text** (list items): each item is a paragraph with a
  bullet, indented by its depth; a long item wraps under its own text,
  not under the bullet.  Its sub-items come below it, one level further
  in, and its closing paragraph after them, at the level of the item's
  text, as written.
- **A free text** (spans `[ ... ]{.p}`, divs `::: p`) shows no structure
  (decision 7 of the proposal): its paragraphs are the paragraphs the
  author wrote, with the colours of the roles only, no bars, no corners.
  A text that mixes the two syntaxes shows its items as a list and its
  spans as text.
- **A text checked by cyp** has a coloured mark in place of the bullet of
  each item: ✔ green, proved (✅); ✘ red, not proved (❌); ◆ orange, left
  to a Proof block (🔶), with the number of its condition; ▫ grey,
  nothing to check: a remark (▫️).  The statement has its mark too, in front of it.
  A span or a div has its mark (a little smaller) inline, at the start of
  its text, where cyp wrote it: the one place where a free text shows
  where a node starts.  cyp's message is in a tinted box where cyp wrote
  it: after the paragraph where its node starts (under the item, for an
  item).  The errors of the tree (a node with no conclusion, a fact not
  in scope, a name that names nothing, a name out of scope, ...) are
  cyp's messages too, with their lines.  The items are numbered in the
  margin, in Dewey notation (`2.1` is the first subnode of `2`), as cyp
  numbers its conditions.  Only a checked text has these numbers: a text
  that is not checked has no use for them.
- **The language** is the `lang` field.  Arabic is written from right to
  left: the bullets, the indentation and the wrapped lines are on the
  right; formulas stay left to right.

### Links

The PDF and the web page have the same links, made with Typst's `link`
and `label` (`links.elpi`, `typst.elpi`, the template's `linked`).  There
are five kinds; the writer finds the first two while it reads the text,
with no table of names (the third and fourth need one, given on the command line).

1. **A name and its uses.**  A name given to a formula, `` `A`{.hyp}
   (h) `` (a hypothesis, or the conclusion of a node that later nodes
   name, `(P1)`), introduces it: the writer gives it a label,
   `statement:h` or `1.2:h` (the number of its node).  Its uses link back to it: the name after a
   fact, `` `A`{.fact} (h) `` (the hypothesis the fact is), a word of the
   text ("By h4 we have", "Applying h2 to h4 and P1", "By IH we have")
   and a justification, `*h*{.just}`.  A name holds where the format
   says ('Scope' above): a hypothesis in the rest of its node and in its
   subnodes; the name of a node's conclusion in the nodes after it and in
   the node around it; the names of the statement in the whole proof; the
   latest introduction wins.  A word is a name only when it is not a
   word of the lexicon of the text's language, so that "a" in French
   "il y a" never links to a hypothesis `(a)`.  This is the same for the
   texts of xtext and for the texts checked by cyp: both are read into
   their tree.
2. **A lemma and its documentation.**  A justification,
   `*Corelib.Init.Datatypes.nat_ind*{.just}`, and a word of the text that Rocq
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
   know where its source is published, unless it is given (below).  A
   tactic (`*lia*{.just}`) has none, unless a table gives one (3.).
   Another library adds its documentation with a clause, as the
   notations are added: `prooftext.library-documentation "MyLib"
   "https://.../"`, if its pages follow rocqdoc's scheme.
   The same clause is given on the command line, without editing a
   file: `pdf.sh --doc-root MyLib=URL` (and `gallery.sh --doc-root`),
   for a documentation made with `rocq doc --html` (one page per file,
   `MyLib.File.html#name`), online or local (`URL` may be relative to
   the page; a relative `URL` given to `gallery.sh` is relative to its
   `OUT`, and rewritten for each page).  A clause given so is added after
   those of the file (`Corelib`, `Stdlib` keep theirs).
3. **A rule or a tactic** (a justification that Rocq does not locate:
   the name of a rule of a checker, a tactic) links to the address that
   a table gives it: `pdf.sh --name-links FILE` (and `gallery.sh
   --name-links`), one line `NAME URL` each, the clauses
   `prooftext.name-url "NAME" "URL"` (`links.elpi`).  A name in scope
   (the name of a hypothesis) comes first.  A word declared in cyp needs
   no table (4.).
4. **A declared justification word** (cyp: `CypJustification "word" :=
   tac.` or `:= rules.`, `cyp/vernac/Cyp.v`) links to its declaration:
   cyp writes, in the JSON next to the checked text (`proof.cyp.json`),
   the declared words that the text uses, each with the file, the
   library and the line of its declaration; `pdf.sh --source-root
   ROOT=URL` (repeatable, and `gallery.sh --source-root`, which copies the
   JSON with the text) turns each into a clause `name-url`, the address
   `URL` + the path under `ROOT` + `#L<line>` (GitHub's line anchors):
   `ROOT` a directory, for a declaration in a file under it (a rule file
   of the proof), or a logical prefix, for one in a library under it
   (`CypV`: `CypV.Cyp` is the file `Cyp.v`, where cyp declares `lia`,
   `tauto`, ...).  No root, no link (the JSON holds the paths of the
   machine that ran cyp).
5. **The pages of a gallery** (`gallery.sh`): see "The gallery".

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
check, the mark of a remark).  Its words are in the language of the text: the uses
`legend-var`, `legend-hyp`, `legend-claim`, `legend-fact`, `legend-just`,
`legend-ok`, ..., `legend-none` of the lexicon, and `legend-goal` (open
goal, but à prouver, ...) for the open goals, listed only in a text that
has one (a proof in progress),, in its ten languages
(`write-word`).  In the web page it is a `footer class="legend"`, and each
role in it is a switch (a check box) that turns the colour of that role on
and off in the whole text (CSS only); the button before them turns them
all off when any is on, else all on, its label ☐ or ☑ being what the next
click does (a few lines of script, `all-script`).

The roles coloured are all of them by default (`var`, `hyp`, `claim`,
`goal`, `fact`, `just`; `pdf.sh` stops on another name); `pdf.sh --roles claim,just`
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
claim`, `formula just`), an item of a list an item of nested lists (`ul
class="steps"`, `li class="step p"`), a paragraph a `p class="para"`, a
status a `span class="mark ok"` (`mark inline ok` at the start of a span
or a div), cyp's message a `div class="message ko"`, the legend a
`footer class="legend"`, the links of a gallery a `nav class="gallery"`,
and a small style sheet, made from the template's colours, gives them
their look (the mark of a role is a border: browsers draw no text
decoration under MathML).  The page needs no file beside it.

**The hover** (decision 8 of the proposal).  Every node is an element of
class `p` with its number, `data-id` (`0` for the top node, around the
statement and the proof; `li` for an item, `span` for a span, `div` for
a div), and a small script at the end of the page (the template's
`hover-script`, about 40 lines) shows, under the pointer, the node and
what it rests on: its conclusion framed, its hypotheses dashed, its
direct subnodes tinted blue, and the formulas that its justifications,
its names and its facts point to outlined in blue (the hypothesis or
the named conclusion a name links to; for a fact, the last hypothesis
or conclusion before it with the same text).  It is the only place where
a free text shows its structure.  The address `page.html#hover=1.2`
fixes the hover on node 1.2, for a screenshot (a headless browser cannot
hover).  Without JavaScript the page is the same, without the hover.

What Typst's HTML export does not do, so that the template does it
itself:

- the layout of the PDF (grids, padding, the page): ignored, with a
  warning each time; hence the lists and the style sheet;
- the colours of text (`text(fill: ...)`), highlights, underlines and
  boxes: dropped; hence the classes;
- labels: kept, but as ids of Typst's own (`loc-N`), see "Links";
- the style sheet and the script go in the body (`html.elem("style")`,
  `html.elem("script")`, written as they are, not escaped), as Typst
  gives no way to add to the `head`; browsers accept it;
- Chrome draws Typst's stretchy parentheses `(x)` with wide gaps; the
  writer therefore writes parentheses that keep their size, `\(x\)`, but
  around a fraction (the same in the PDF).  The arguments of an application
  are then separated by escaped commas, `f\(x\, y\)`: between `\(` and
  `\)`, which are not a group, a plain comma inside the arguments of a
  Typst function (`frac(f\(x, y\), 2)`) would separate them (an error,
  "unexpected argument", seen on a text of cyp).

The page was looked at in Chrome (headless screenshots) for a text of
xtext, a checked text with its statuses and messages, and the unit tests
of the printer; with the links and the new look of the roles, for
`drinker`, `or_commut` in French and the pages of a small gallery; with
the hover, for the proposal's examples in both syntaxes, checked and not
(`#hover=...`).  Firefox was not tried.

### Tests

`sh prooftext/typst/check.sh` (about 90 s, with cyp built; needs `qpdf`):

1. for the ten texts that xtext writes in Typst (`xtext/examples-typst/`:
   five in English, one each in French, Arabic, Chinese, Russian and
   Korean), the Typst source read back from their Markdown text
   (`xtext/examples/`) is the same, character for character; (xtext writes
   them through their Markdown, read back: they differ only if the
   Markdown does not read back as written);
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
7. the two syntaxes: the proposal's examples `praeclarum` (the
   paper's), `xtext_praeclarum` and `Trans_Inv`, structured and free:
   their PDF and their web page, each node an element of class `p` with
   its number, the script of the hover, the same nodes in both syntaxes,
   the closing paragraph after the sub-items, a free text as paragraphs
   and spans;
8. the round, when cyp is built: xtext's `or_commut` checked by cyp, then
   the PDF of the checked text; cyp's `sqrt_square` (real numbers)
   checked, then its PDF and its HTML page; xtext's proof in progress
   `praeclarum_partial1` checked (its open goals left, ◆), then its PDF
   and its HTML page (the goals framed, `#goal`, and in the legend);
9. the links, on a small gallery of four pages built in
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
the stdlib (`Nat.lt_eq_cases`), a tactic (no link), the legend in
English and French, and the Typst writer on a tree: a checked free text
(its spans, their marks, cyp's messages matched to their nodes) and the
closing paragraph of an item after its sub-item.

### Limits

- A formula without a class is plain text: shown without a role (cyp
  does not use it either).
- The errors of the tree (an unclosed div, a node with no conclusion,
  ...) are shown only in a checked text, as cyp's messages; the PDF of a
  text that is not checked shows the text as it reads it, without them.
- In a checked free text, nodes that start at the same place show their
  marks side by side (✔ ✔ We have ...), one per node.
- The hover finds the formula a fact repeats by its text (the last
  hypothesis or conclusion before it with the same text), not by
  conversion as cyp does.
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
   a class that has the form of a declaration, but not one that starts
   with a binder, `forall z : A, P z`) puts its variables in the
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
82 English texts of xtext and the 11 of cyp's examples (1978 formulas,
measured 2026-11-19 with `pdf.sh --source`), 2 formulas are shown as code
(`n` and `l1`, bound by a `fix` that no `Let` declares).  Before the tree,
on 79 + 8 texts (2090 formulas), the same 2, and 1 formula had a part in
Rocq's text (a `match`; not counted again).

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
  pages of `pdf.sh`); xtext's `ExtractText foo to "foo.typ"` has its own
  program, where they are added the same way (`Elpi Accumulate ExtractText`).
- In a PDF, a word operator (div, mod) inside a highlighted formula has
  its own highlight box; inline fractions are small (Typst's inline
  maths).
