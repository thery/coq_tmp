// Revisiting Cyp and extracting text from proofs
// Build: typst compile notes/revisiting-cyp/main.typ

#set document(title: "Revisiting Cyp and extracting text from proofs", author: "Laurent Théry")
#set page(paper: "a4", margin: (x: 2.4cm, y: 2.5cm), numbering: "1")
#set text(font: "Libertinus Serif", size: 10.5pt, lang: "en", region: "gb")
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: set block(above: 1.3em, below: 0.7em)
#show raw: set text(font: "DejaVu Sans Mono", size: 8pt)
#show raw.where(block: true): it => block(
  fill: luma(246), inset: 7pt, radius: 2pt, width: 100%, align(left, it))
#show figure: set block(breakable: false)
#show figure.caption: set text(size: 9pt)
#show link: set text(fill: rgb("#0072b2"))

#align(center)[
  #text(size: 17pt, weight: "bold")[Revisiting Cyp and extracting text from proofs]
  #v(0.4em)
  #text(size: 12pt)[Laurent Théry]
  #v(0.2em)
  #text(size: 9.5pt)[Inria — November 2026]
]

#v(0.8em)
#block(inset: (x: 1.2cm))[
  #set text(size: 9.5pt)
  *Abstract.* In 2003 we proposed Cyp, a format in which a proof is
  written as ordinary text and its formulas are tagged as hypotheses,
  conclusions or variables, so that each step of the text becomes a
  condition for a prover. This note describes a new implementation of
  the idea for Rocq, and a tool that goes the other way. *cyp* reads a
  proof written in Markdown and checks each step in Rocq. *xtext* writes
  such a text from a Rocq proof term, after Coscoy's thesis. Both tools
  are written in Rocq-Elpi and share a library for the format, a lexicon
  of ten languages and a back end that typesets the texts with Typst. We
  report what was built, how, and what we measured: of the 683 steps
  with a claim in the 80 English texts written by xtext, cyp proves 666.
]

= Introduction

The paper _Colouring proofs_ @thery2004colouring came from proofs of
floating-point algorithms. The proof was first written on paper. Then it
was redone as a Coq script. The two then went separate ways. The paper
listed three consequences. The published proof is not the checked
one: only its statement is. The script tells little about the structure
of the proof, which makes it hard to maintain. And when a hypothesis is
changed, the failing tactic does not say which step of the paper proof
is wrong.

The proposal was a light one. Keep the proof as text, as a
mathematician writes it. Mark only its structure and the role of each
formula: what is assumed, what is proved, which variables are
introduced. The structure is the one Lamport asks of a proof
@lamport1995how: a statement decomposed into steps until each step is
obvious. A tool then reads the marked text as a verification
condition generator reads an annotated program: each step
gives a lemma, and the text is checked when every lemma is proved. The
marking was done in a small graphical interface, by selecting a piece
of text and giving it a colour. Hence the name, Cyp, for _Colour Your
Proof_.

The 2003 tool did little checking. Every generated lemma was closed by
an axiom, `Apply ok`, so that the generated file was only type-checked.
Proving the conditions was left to the user. The conclusion of the paper
also asked whether such texts could be produced from formal proofs, as
in the earlier work on extracting text from proofs
@coscoy1995extracting @coscoy2000thesis.

This note revisits both directions, twenty years later, for Rocq.

- *cyp* reads a proof written in Markdown, with its formulas in Rocq
  syntax, builds the conditions of its steps, and tries to prove each
  of them. It writes the text back with a status in front of each step.
- *xtext* writes a proof text from a Rocq proof term. It follows the
  staged translation of Coscoy's thesis @coscoy2000thesis. Its output is
  in the format that cyp reads.
- *prooftext* and the *lexicon* are what the two share: the document
  tree, its reader and writer, the roles of formulas, the words of ten
  languages, and a back end that makes a PDF or a web page of a text.

Everything is written in Rocq-Elpi @dunchev2015elpi, the extension
language of Rocq based on λProlog. There is no external parser and no
second implementation of the format.

We do not claim that the texts are good prose. The texts of xtext are
faithful but coarse. The languages other than English were never
reviewed by a native speaker. A step that cyp proves is a step whose
claim follows from what comes before it; cyp does not check that it
follows _for the reason the text gives_. These limits are recalled where
they matter.

The note is organised as follows. @sec-format describes the format,
from the 2003 tags to Markdown, and the format we are now implementing.
@sec-cyp describes the checker, @sec-xtext the writer, @sec-shared the
shared libraries and the languages, and @sec-render the PDF and the web
pages. @sec-experience gives the measurements. @sec-related and
@sec-conclusion discuss related work and what remains to be done.

= The format <sec-format>

== The 2003 format: seven tags

The 2003 format had seven XML tags: `p` for a proof or a subproof, `c`
for its conclusion, `h` for a hypothesis, `v` for a variable, `n` for a
name, `f` for a formula, and `j` for a justification. Each `p` had
exactly one conclusion, at most one name and one justification, and any
number of variables, hypotheses and subproofs. A hypothesis and a
variable were visible in their proof and its subproofs. A subproof
could use the conclusions of the subproofs before it.
@fig-2003 shows the classic _praeclarum theorema_ in this format, and the
interface where the tags were shown as colours: red for names, green for
what is assumed, blue for what is proved.

#figure(
  grid(columns: (1.15fr, 1fr), gutter: 10pt, align: horizon,
    raw(read("figures/praeclarum.2006.xml").trim(), block: true, lang: "xml"),
    image("figures/cyp2003.png", width: 100%),
  ),
  kind: image,
  caption: [Left: _praeclarum_ in the 2003 format (the file of the 2003
  examples, unchanged). Right: the 2003 interface on another example of
  the paper, `exp_pos`, cropped from the published figure.],
) <fig-2003>

== Today: Markdown with roles

The 2003 format had two practical problems. The XML tags make a text
hard to read without the tool. And every formula had to be tagged by
hand. Today's format is plain Markdown, and the role of a formula is
read from the words before it. @fig-today gives _praeclarum_ in it.

#figure(
  {
    show raw: set text(size: 6.6pt)
    grid(columns: (1fr, 1fr), gutter: 8pt,
      raw(read("figures/praeclarum_words.md").trim(), block: true),
      raw(read("figures/praeclarum_words.checked.md").trim(), block: true),
    )
  },
  kind: image,
  caption: [_praeclarum_ in today's format (left), and the file that cyp
  writes back (right). ✅ marks a step proved, ▫️ a step with nothing to
  check. The roles come from the words _Let_, _If_, _then_, _Suppose_,
  _We have_, _hence_. The same text with a class on each formula
  (`{.var}`, `{.hyp}`, `{.claim}`) gives the same result.],
) <fig-today>

A text has a header between two lines `---` (the Rocq libraries to load,
the default tactics, the language), a title `# name`, a statement, and
a nested list of steps. A formula is written between backticks in Rocq
syntax. Its role comes from the phrase before it: _let_ introduces
variables, _if_ and _assume_ hypotheses, _from_ and _using_ facts that
are mentioned, _we have_, _hence_, _so_ claims. A class written after the
formula, `{.claim}`, gives the role explicitly; this is the attribute
syntax of Pandoc. A step names its justification as a paper says "by
Lemma 3": `*by X*`, where X is a lemma, a hypothesis, a named rule or a
tactic. @tab-tags maps the 2003 tags to this format.

#figure(
  table(columns: 2, align: left, stroke: 0.4pt + luma(180), inset: 5pt,
    table.header([*2003*], [*today's Markdown*]),
    [`<p>` a proof or a subproof], [a list item, its sub-steps indented below it],
    [`<n>` a name], [the title `# name`; for a hypothesis, `(h)` after its formula],
    [`<c>` the conclusion], [#raw("`F`{.claim}"), or after _we have_, _we prove_, ...],
    [`<h>` an assumption], [#raw("`F`{.hyp}"), or after _assume_, _if_, ...],
    [`<v>` a variable], [#raw("`x : T`{.var}"), or after _let_],
    [`<f>` a formula used], [#raw("`F`{.fact}"), or after _from_, _using_, ...],
    [`<j>` a justification], [`*by X*`: a lemma, a hypothesis, a rule or a tactic],
  ),
  caption: [The tags of 2003 and their form in today's Markdown.],
) <tab-tags>

Today's format also departs from 2003 in its structure. A step may have
several claims (_we have `x` and hence `z`_), each proved from the ones
before it. A step that says _it suffices to prove_ goes backwards: its
claim replaces the goal. And a step that only introduces variables or
hypotheses opens a scope for its sub-steps, which is how the cases of an
induction are written.

== The format being implemented: the 2003 tree, two syntaxes <sec-v2>

Guessing roles from words was convenient, but it has costs. The reader
needs a list of phrases for every language. A formula can take a role
that the author did not mean. And the Typst writer does not guess roles,
so an untagged formula has no colour in the PDF (@fig-maths below).
Several claims per step and the backward keywords also took the format
away from the tree of 2003, where each proof has one conclusion.

We have therefore decided on a new format, which is now being
implemented. At the time of writing no reader exists for it: the
examples below are written by hand, and the figure is a hand-written
Typst mock-up. The decisions are the following.

- Only what is tagged is used. An untagged formula is plain text, shown
  without colour and ignored by cyp.
- The tree of 2003 comes back: one conclusion per node, subnodes,
  and scopes for hypotheses and variables. A node is seen from outside
  as $forall V, H -> C$, and a node may use the conclusions of the nodes
  before it, at every level (the visibility rule of 2003).
- A justification is a name in the sentence, emphasised and tagged like
  a formula: `By definition of and (*conj*{.just}), we have ...`. A node
  may have several, since a sentence may name several things
  (`Applying *i*{.just} to *k*{.just}`). This departs from 2003, which
  had one `j` per proof.
- There are two syntaxes for the same tree. In the _structured_ syntax a
  list item is a node and its sub-items are its subnodes; a paragraph
  after the sub-items belongs to the item, so that a conclusion can come
  after its subproofs. In the _free_ syntax a node is a Pandoc span
  `[…]{.p}` inside a paragraph, and spans nest. A list item is read as a
  span around its contents, so the two syntaxes can be mixed.

#figure(
  grid(columns: 1, gutter: 6pt,
    raw("- Suppose `x /\\ y`{.hyp}.
  - We get `z`{.claim} by `x -> z`{.fact}, since
    - we have `x`{.claim}.
  - We get `t`{.claim} by `y -> t`{.fact}, since
    - we have `y`{.claim}.

  Altogether we have `z /\\ t`{.claim}.", block: true, lang: "markdown"),
    raw("[Suppose `x /\\ y`{.hyp}. [[We have `x`{.claim}]{.p}, so by `x -> z`{.fact}
we get `z`{.claim}.]{.p} [[We have `y`{.claim}]{.p}, so by `y -> t`{.fact}
we get `t`{.claim}.]{.p} Altogether we have `z /\\ t`{.claim}.]{.p}", block: true, lang: "markdown"),
    image("figures/fig-mockup-praeclarum.png", width: 88%),
  ),
  kind: image, placement: auto,
  caption: [The proof of _praeclarum_ in the format being implemented:
  structured syntax (top), free syntax (middle), and the hand-written
  mock-up of the structured one (bottom). Variables are sky blue,
  hypotheses orange, conclusions yellow, facts grey. The free syntax
  reproduces the 2003 line `<p><p> we have <c>x</c></p>, so <j>by <f>x
  -> z</f></j>, we get <c>z</c></p>` node for node.],
) <fig-v2>

One limit is known in advance: Pandoc has no attributes on emphasis, so
a Markdown preview shows `*conj*{.just}` with its `{.just}`. prooftext
reads Markdown itself, so the PDF and the web page are not affected.

The cost of the change is also known, since it was counted on the 82
English texts of xtext (1201 list items): 179 items name a
justification with `*by X*`, 124 items have hypotheses but no claim and
must be merged with a sub-item, 141 items have both a claim and a fact,
and 384 items have facts only (321 of them are "The element `z` belongs
to `E`", whose "facts" are not formulas). All of cyp's examples must be
retagged, since 8 of the 10 rely on keywords only.

= Reading and checking: cyp <sec-cyp>

== The text as a verification condition generator

cyp is a Rocq-Elpi command, `CypFile "proof.md".` A small OCaml driver
writes the Rocq file that loads the libraries of the header and runs the
command. The command reads the Markdown, elaborates each formula in the
context of its step (with `coq.parse.argument`), and builds one
condition per claim. The conditions are numbered after their step, in
Dewey notation: `1.1a` and `1.1b` are the two claims of the first
sub-step of step 1, and `0` is the statement after the steps.
@fig-conditions shows two of the six conditions of _praeclarum_, as
printed by `cyp --conditions`, beside the 2003 lemmas for the paper's
`exp_pos`. The structure is the same: the context of a condition holds
the variables and hypotheses in scope and the claims of the steps
before it. The difference is that the 2003 lemmas ended with `Apply ok`,
and cyp tries to prove its conditions.

#figure(
  grid(columns: (1fr, 1fr), gutter: 10pt,
    raw("  x y z t : Prop
  H1 : x -> z
  H2 : y -> t
  H3 : x /\\ y
  c1_1a : x
  ============================
  z

  ...
  H1 : x -> z
  H2 : y -> t
  c1a : x /\\ y -> x
  c1b : x /\\ y -> z
  c1c : x /\\ y -> y
  c1d : x /\\ y -> t
  c1e : x /\\ y -> z /\\ t
  ============================
  x /\\ y -> z /\\ t", block: true),
    raw("Lemma c_gp_2: (x: Z) (y: Z)
  (Zlt ZERO x) -> (`0` = y) ->
  (exp x y) = `1`.
Proof.
Intros x y gh_1.
Generalize (c_gp_1 x y gh_1);
  Intros gp_1.
Intros gh_2_1.
Apply ok.
Qed.", block: true),
  ),
  kind: image,
  caption: [Left: conditions 1.1b and 0 of _praeclarum_ (output of
  `cyp --conditions`, the four variable lines merged into one). Condition 0
  sees the claims of the scope of step 1 generalised over its hypothesis.
  Right: a lemma generated in 2003, from the appendix of
  @thery2004colouring.],
) <fig-conditions>

cyp builds the proof term itself. A forward claim is a `let` over the
proof of the claim; a backward step is a proof of $C -> G$ applied to a
proof of $C$; a scope is a proof of its claims generalised over its
variables and hypotheses. The term is then type-checked by Rocq and the
lemma is defined, so `Print Assumptions` shows only the axioms of the
libraries used. A first version built one copy of a scope's proof per
claim, and the term grew quickly with the nesting. It now gives
the proof of several claims once and projects each claim out of it. On
a test of 12 nested steps of two claims, type-checking and definition
went from 31.7 s and 12.1 s to 37 ms and 35 ms.

== How a condition is closed

A condition is tried, in order, with:

+ the step's justification, when it has one. A name of rules runs those
  rules only. A hypothesis or a lemma is applied, and its premises are
  closed by the rules and the default tactics. A tactic name runs the
  tactic;
+ the rules of the proof. A rule is an Elpi clause in a file named in
  the header, for instance
  ```
  justify {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat }}).
  ```
  which applies a monotonicity lemma to a goal of that shape. This is
  where the knowledge of a field goes: rules are written once per field,
  not in cyp. A rule may also have a name, and a step that says _by
  monotonicity_ is then closed by that rule and no other;
+ the default tactics of the header (`by: lia | nia`). For the name
  `tauto` cyp runs itauto @besson2021itauto, because `tauto` can run for
  minutes on small goals that itauto closes at once. For `firstorder`
  it runs a bounded search: the unbounded tactic took more than 30 s and
  7 GB of memory on one step of a text;
+ a last, coarse _gap tactic_: a few bounded searches (taking the goal
  and hypotheses apart, then a search of depth 4 or `congruence`, case
  analysis on booleans or on a variable, induction on a binder of the
  goal, a constructor). A condition it cannot close costs at most
  0.06 s (measured). On the conditions that the steps before leave open
  in xtext's texts, it closes 99%.

A claim that does not hold is still added to the context of the steps
after it, as on paper. A wrong step therefore makes the next steps
easier, and the red step is the one to look at first.

== The result, and the conditions left to the user

cyp writes the text back with a status in front of each step (✅ proved,
❌ not proved, ▫️ nothing to check), and under a failing step a folded
block with the goal and Rocq's message. It also writes a JSON file that
a VS Code extension (about 130 lines of JavaScript) uses to colour the
formulas by role and to show the goal of a failing step on hover. The
lemma is defined only when every step is proved.

The conditions that cyp does not discharge can be left to ordinary
tactics. With `Cyp File "proof.md". Proof. ... CypQed.`, each open
condition is a goal named after its number, and the script proves it by
name with Rocq's goal selectors:

```
Cyp File "vc_file.md".
Proof.
  [c1b]: apply Z.sqrt_nonneg.
  [c1a]: apply Z.sqrt_nonneg.
CypQed.
```

The step is then marked 🔶 with the numbers of its conditions. The same
proof can also be written as a Rocq command, `Cyp Lemma`, whose body is a
list of words and Rocq terms. A text may be written in any of the ten
languages of the lexicon (@sec-shared).

= Writing: xtext <sec-xtext>

`Explain foo.` prints the proof of the constant `foo` as a text. It
follows the basic transducer of @coscoy1995extracting, extended to
inductive types after Coscoy's thesis @coscoy2000thesis. Proofs ending
with `Qed` work too, since Rocq-Elpi gives the body of opaque constants.
The text is in the format of @sec-format: one list item per step, every
formula in backticks with its role class, and the lemma or rule used by
each step. It is meant to be faithful, not fluent: rewriting it into
prose is left to a later pass, by hand or by a language model.

== The staged translation

By default a proof term becomes text in the three stages of the thesis,
each a predicate on its own data type, so that each can be read against
its figure.

+ *Annotation* (thesis 3.3.4). Each node of the term gets the type it
  proves, partly synthesised, and the type required at its place,
  inherited from the statement.
+ *Contraction* (thesis 2.3 and 3.4.2). Nested applications and series
  of abstractions are merged. The contraction can be `none`, `maximal`,
  or `guarded`: only the merges that drop a single annotation, so that no
  conversion step disappears. With another switch this stage is the
  _selection_ of type annotations of the thesis (4.3.1), followed by the
  naming of intermediate results (4.3.2–4.3.3): each subproof used in an
  application becomes a step of its own, named P1, P2, ..., before the
  step that uses it.
+ *Writing*. A conclusion says the type it proves, then "that is" the
  required type when they differ.

The forms that the thesis treats in its chapter 6 (eliminations,
introductions, rewriting, `fix`) are written directly, and their
subproofs come back to the stages. Elimination and introduction theorems
are recognised by their type, not their name. The motive of a dependent
elimination is left out when Rocq's `elim` would find it again (thesis
6.4.1). A subproof built by a tactic is one step "by T" (thesis 5.4).
@tab-sizes gives the sizes of the texts with each choice of the second
stage, on the 73 texts that are not proofs in progress.

#figure(
  table(columns: 3, align: (left, right, right), stroke: 0.4pt + luma(180), inset: 5pt,
    table.header([*second stage*], [*list items*], [*characters*]),
    [contraction none], [1778], [221 981],
    [contraction maximal], [1128], [118 180],
    [contraction guarded (default)], [1164], [126 128],
    [selection (thesis 4.3.1)], [981], [112 964],
  ),
  caption: [Sizes of 73 texts written by xtext with each second stage.],
) <tab-sizes>

The cost of the selection is easy to state. The statement of a
hypothesis or a theorem used by name is no longer repeated, so a reader
must know or look up the statement of a library lemma. A file,
`THESIS.md`, maps each rule and figure of the thesis to the predicate
that implements it and to the example that reproduces it; test files
check the selected terms of the thesis's figures (Fig. 4.24, 4.27, 4.17)
against the expected ones.

== An example

The Rocq term of _praeclarum_ used by xtext is
```
fun x y z t h1 h2 =>
  and_ind (fun (i : x -> z) (j : y -> t) =>
    and_ind (fun (k : x) (l : y) => conj (i k) (j l)) h2) h1
```
and xtext writes
```
Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (h1)
and `x /\ y`{.hyp} (h2). We prove `z /\ t`{.claim}.

- Going back to the definition of and (and_ind) in
  `(x -> z) /\ (y -> t)`{.fact} (h1), we prove `z /\ t`{.claim}:
  - Assume `x -> z`{.hyp} (i) and `y -> t`{.hyp} (j).
    - Going back to the definition of and (and_ind) in `x /\ y`{.fact} (h2),
      we prove `z /\ t`{.claim}:
      - Assume `x`{.hyp} (k) and `y`{.hyp} (l).
        - Applying i to k, we have `z`{.claim}.
        - Applying j to l, we have `t`{.claim}.
        - So by definition of and (conj), we have `z /\ t`{.claim}
          *by Corelib.Init.Logic.conj*.
```
(lines broken here for the page; xtext writes one line per item). cyp
checks this text in full. The same proof in the format being
implemented is in @fig-xtext-v2: the justifications are the names
already in the sentences, and the last line becomes the closing
paragraph of its node.

#figure(
  image("figures/fig-mockup-xtext.png", width: 92%),
  caption: [xtext's _praeclarum_ in the format being implemented
  (hand-written mock-up; the justifications are purple).],
) <fig-xtext-v2>

= Shared libraries and languages <sec-shared>

cyp and xtext do not depend on each other. What they must agree on is in
two libraries.

- *prooftext* holds the document tree and its writer, the reader of a
  Markdown text (with the places of its lines, for error messages), the
  header and its fields, the roles and how a formula carries its role,
  the justification, fresh names, the tactics a text may name, and the
  marks of a checked text. A writer and a reader that disagree on a
  detail is the first thing that goes wrong when two tools share a
  format; here there is one reader, and a test reads back what the
  writer writes.
- The *lexicon* holds, per language, the phrases that give a role to
  the formula after them (`phrase Lang Phrase Role`) and the phrases of
  the writer. A writer's phrase that gives a role is also a reader's
  phrase, by one clause, so cyp reads a role exactly as xtext means it.

xtext writes a sentence as a list of parts (phrases by their use,
formulas, names), and only the table changes from one language to
another. The lexicon has ten languages: English, French, Italian,
German, Dutch, Russian, Chinese, Arabic, Korean and Latin. The tables
also handle what is not English-like: Chinese has no spaces, Arabic has
clitics and is written from right to left, and in Korean the phrase
comes after its formula. @fig-ar shows the Arabic text of _praeclarum_.
Two plain limits: no phrase was checked by a native speaker, and the
word order is otherwise the English one (the Korean texts keep the
English order of the words that give no role).

#figure(
  image("figures/fig-praeclarum-ar.png", width: 88%),
  caption: [xtext's _praeclarum_ in Arabic, as typeset by prooftext. The
  formulas stay left to right. The word _by_ before the justification is
  part of the format and is not translated.],
) <fig-ar>

All of this is Elpi code loaded by Rocq: about 1230 lines for cyp's
reader and checker, 2740 for xtext, 2160 for prooftext (including the
printer of formulas and the Typst writer) and 1000 for the lexicon
(counted with `wc -l`, comments included).

= Rendering <sec-render>

== PDF and web page

A proof text is typeset with Typst @typst. The Typst writer is in Elpi,
next to the Markdown writer, so a text that xtext has just built is
written directly, and a Markdown text (written by xtext, checked by cyp,
or written by hand) is first read by the shared reader. The look is a
Typst template, in one place. A web page is made from the same Typst
source with Typst's HTML export (experimental in Typst 0.15); its
formulas are MathML, and it needs no JavaScript.

== Formulas as mathematics

A formula is a Rocq string. For the PDF it is elaborated in Rocq, after
the `require` line of the text, then printed as a tree of mathematical
notation (operators with their levels, fractions, powers, roots,
delimiters, quantifiers grouped by type), then written as Typst maths. A
table, extensible by a library with Elpi clauses, gives the notation of
each constant: `Rdiv` is a fraction, `Rabs` is $|dot|$, `Datatypes.nat`
is $NN$. On the 79 texts of xtext and the 8 of cyp's examples then
available (2090 formulas), 2 formulas could not be elaborated and are
shown as code (variables bound by a `fix` that no `Let` declares).
@fig-maths shows a text on real numbers checked by cyp.

#figure(
  image("figures/fig-sqrt-square.png", width: 92%),
  caption: [A text of cyp's examples on real numbers, checked by cyp and
  typeset. Its formulas carry no class, so they have no role colour. The
  word _value_ is linked because it is also the name of a constant of
  Rocq's corelib: a known limit of the links.],
) <fig-maths>

== Roles, statuses and links

The role of a formula is a light background behind black text: sky
blue for variables, orange for hypotheses, yellow for claims, grey for
facts, and a reddish purple for the name in a justification. They are
light tints of the Okabe–Ito palette, with no red–green pair. We checked
the pages under simulations of protanopia, deuteranopia and tritanopia
@machado2009cvd: the roles stay distinct. Since colour alone is not
enough, the legend at the end of a text also gives each role a mark that
needs no colour (a dashed line, a frame, a dotted line). A checked text
has a mark per step in place of the bullet (✔ proved, ✘ not proved, ◆
left to a Proof block, ▫ nothing to check), cyp's message in a box under
a failing step, and the step numbers in the margin, as cyp numbers its
conditions (@fig-drinker).

The PDF and the web page have links. A name given to a hypothesis,
`(h)`, labels its step, and its later uses link back to it. A lemma
that Rocq locates in the corelib or the stdlib links to its entry in
the online documentation. A word of the lexicon is never a name, so
the French "a" is not taken for a hypothesis `(a)`.

A gallery of every text of the repository, with their PDFs and web
pages, is published at #link("https://thery.github.io/coq_tmp/txt/")
(387 texts in its last build).

= Experience <sec-experience>

== xtext's texts checked by cyp

The texts written by xtext carry the role of every formula and the
lemma of every step, so cyp can check them. This is a test of both
tools: it fails when xtext writes a wrong formula, a wrong role or a
wrong scope, and when cyp reads one wrongly. Each text is checked alone,
with at most 8 GB of memory and 300 s.

#figure(
  table(columns: (2.4fr, 1fr, 1fr, 1fr, 1.2fr, 1fr),
    align: (left, right, right, right, right, right),
    stroke: 0.4pt + luma(180), inset: 5pt,
    table.header([*set*], [*texts*], [*proved*], [*not proved*], [*nothing to check*], [*time*]),
    [English, staged (default)], [80], [666], [17], [504], [176 s],
    [English, direct translation], [72], [923], [23], [213], [595 s],
    [each of 9 other languages], [12], [77], [1], [38], [21–26 s],
  ),
  caption: [cyp on the texts of xtext (staged texts: runs of 2026-11-19;
  direct translation: run of 2026-11-18). Counts are list items. A step
  has "nothing to check" when it has no claim (_Let_, _Assume_, the
  announcement of an induction). The direct translation had 5 timeouts;
  the staged one has none.],
) <tab-results>

On the 80 English texts, cyp proves 666 of the 683 steps with a claim
(97.5%). The 17 others are in 7 texts. @fig-drinker shows one of them:
in the drinker's paradox, the step "Applying not_all_ex_not to A, P and
H" is not proved. The text names the lemma in its sentence but has no
`*by*` justification, and the header of the text does not even import
the classical library that defines it: xtext writes the same `require`
line for every text, a known limit.
The two English texts left out are the texts on real numbers of the
PDF tests. In the nine other languages, every step has the status of the
same step in English, in all 108 texts: no step is proved in one
language and not in another.

#figure(
  image("figures/fig-drinker-checked.png", width: 96%),
  caption: [The drinker's paradox: the text written by xtext from a
  proof by `destruct`, `exists` and a classical lemma, checked by cyp
  (run again for this note, identical to the stored result) and
  typeset. Step 4.1.1 is not proved.],
) <fig-drinker>

These results say less than they seem. cyp proves each claim again with
its own tactics; a green step means that the claim follows from its
context, not that it follows the way the sentence says. Making the text
the actual proof would need cyp to use the named justification and
nothing else, as it already does for named rules.

== What the measurements changed

Several choices came from measurements rather than from design.

- *Bounded tactics.* Unbounded `firstorder` caused most of the timeouts
  and memory blow-ups on xtext's texts, and `tauto` ran for minutes on
  a goal two hypotheses long. cyp now first checks whether a goal is one
  of its hypotheses, runs itauto for `tauto`, and bounds `firstorder`.
- *The gap tactic.* Its searches were chosen in a greedy order over the
  conditions left open by the English texts, each candidate tried on
  each open condition.
- *Tags or words.* Reading every text twice, with and without its
  classes, shows that on 94 of 1933 lines of the English texts the role
  of a formula comes only from its class: words are not enough even for
  texts written by a program from a fixed vocabulary. This was one of
  the reasons for the decision of @sec-v2 to use tags only.

== A case study

The format was also used on a floating-point case study of about 600
steps checked by cyp. This work is not public, and we only report its
size here.

= Related work <sec-related>

*Text from proofs.* xtext is a new implementation of the work of
Coscoy, Kahn and Théry @coscoy1995extracting and of Coscoy's thesis
@coscoy2000thesis, for today's Rocq. What it adds is the format: its
texts can be read back and checked by a separate tool. The thesis's
chapter 4 also describes scripts, texts that can be read back into proof
terms; xtext does not implement them.

*Declarative proof languages.* Mizar @bancerek2015mizar and Isar
@wenzel1999isar are languages in which a proof is a structured text with
its formulas, checked by the system. Coq had a declarative mode, C-zar
@corbineau2008declarative. These languages have a fixed syntax, and the
proof must be written at the level of detail the checker needs. The
format here is closer to the 2003 aim: the text is ordinary prose with
marked formulas, a step may be as coarse as automation allows, and a
step that is not proved is reported rather than rejected.

*Controlled natural language.* Naproche @cramer2010naproche checks
mathematical texts written in a controlled natural language, with
automated provers for the steps. Verbose Lean @massot2024verbose gives
Lean tactics in a controlled natural language, in English and French,
for teaching. In both, the words are the syntax. In cyp, the words are
free and the syntax is in the marks (and in today's format, partly in
a list of phrases); in the format being implemented, only the marks
count.

= Conclusion and future work <sec-conclusion>

The idea of 2003 survives the change of tools. A proof written as text,
with marked formulas, gives conditions that a prover can discharge, and
today's automation discharges most of the small ones. Writing such
texts from proof terms, and checking them with the same format, is a
cheap test of both directions.

What remains, in order:

- implement the format of @sec-v2 in prooftext, cyp and xtext, and
  regenerate the texts (190 texts of xtext in all languages and cyp's
  examples);
- make cyp use the named justification of a step, so that a proved step
  follows for the reason given;
- the parts of the paper and the thesis that xtext does not implement:
  the "further optimisations" of @coscoy1995extracting, the specific
  wordings for connectives and classical reasoning, the scripts of the
  thesis's chapter 4, mutual fixpoints;
- a review of the phrases of each language by native speakers;
- turning xtext's faithful texts into fluent prose while keeping them
  checkable, which the format makes possible: a rewritten text is checked
  again by cyp.

The code is in the repository `coq_tmp` (directories `cyp`, `xtext`,
`prooftext` and `lexicon`).

#bibliography("refs.bib", style: "springer-basic-author-date", title: "References")
