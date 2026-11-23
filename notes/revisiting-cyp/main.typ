// Revisiting Cyp and extracting text from proofs
// Build: typst compile notes/revisiting-cyp/main.typ
// The figures and the outputs of the tools are made by figures/make.sh.

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

// lines [a, b) of a file written by a tool (figures/make.sh)
#let lines(file, a, b) = read(file).split("\n").slice(a, b).join("\n")

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
  proof written in Markdown and checks each step in Rocq; it never fails
  as a whole, and leaves the steps it cannot prove as named goals.
  *xtext* writes such a text from a Rocq proof term, after Coscoy's
  thesis. The format is the tree of the 2003 paper, written either as
  nested lists or as free prose with marked spans; only what is tagged
  is used, and the justifications are tagged names in the sentences,
  whose meaning is declared in the files of the proof. Neither tool has
  a time limit: every search has a fixed bound, so a verdict does not
  depend on the machine. Both tools are written in Rocq-Elpi and share
  a library for the format, a lexicon of ten languages and a back end
  that typesets the texts with Typst, as a PDF or as a web page. We
  report what was built and what we measured: in the 80 English texts
  written by xtext, cyp proves 650 of the 652 steps it tries (666 of 683
  with the format used before).
]

= Introduction

The paper _Colouring proofs_ @thery2004colouring (UITP 2003) came from
proofs of floating-point algorithms. The proof was first written on
paper. Then it was redone as a Coq script. The two then went separate
ways. The paper listed three consequences. The published proof is not
the checked one: only its statement is. The script tells little about
the structure of the proof, which makes it hard to maintain. And when a
hypothesis is changed, the failing tactic does not say which step of the
paper proof is wrong.

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
  syntax, builds the condition of each step, and tries to prove it. It
  writes the text back with a status in front of each step.
- *xtext* writes a proof text from a Rocq proof term. It follows the
  staged translation of Coscoy's thesis @coscoy2000thesis. It prints the
  text plainly, or writes it in the format that cyp reads.
- *prooftext* and the *lexicon* are what the two share: the reader of
  the format into its tree, the writer, the roles of formulas, the words
  of ten languages, and a back end that makes a PDF or a web page of a
  text.

Everything is written in Rocq-Elpi @dunchev2015elpi, the extension
language of Rocq based on λProlog. There is no external parser and no
second implementation of the format.

We do not claim that the texts are good prose. The texts of xtext are
faithful but coarse. The languages other than English were never
reviewed by a native speaker. A step that cyp proves is a step whose
conclusion follows from what it can see; cyp does not check that it
follows _for the reason the text gives_. These limits are recalled where
they matter.

The note is organised as follows. @sec-format describes the format,
from the 2003 tags to the tree in Markdown that the tools now use.
@sec-cyp describes the checker, @sec-xtext the writer, @sec-shared the
shared libraries and the languages, and @sec-render the PDF and the web
page. @sec-experience gives the measurements. @sec-related and
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
    raw(read("figures/praeclarum.2003.xml").trim(), block: true, lang: "xml"),
    image("figures/cyp2003.png", width: 100%),
  ),
  kind: image,
  caption: [Left: _praeclarum_ in the 2003 format (the file of the 2003
  examples, unchanged). Right: the 2003 interface on another example of
  the paper, `exp_pos`, cropped from the published figure.],
) <fig-2003>

== A first Markdown version, and why it changed

The XML tags make a text hard to read without the tool, and every
formula had to be tagged by hand. The first version of cyp therefore
read plain Markdown, with formulas between backticks, and took the role
of a formula from the words before it: _let_ introduced variables, _if_
and _assume_ hypotheses, _we have_ and _hence_ claims. A step could have
several claims (_we have `x` and hence `z`_), a step that said _it
suffices to prove_ went backwards, and a justification was written
after the sentence, `*by X*`.

Guessing roles from words had costs. The reader needed a list of phrases
for every language, a formula could take a role the author did not
mean, and the Typst writer, which did not guess, showed such formulas
without colour. Several claims per step and the backward phrases also
took the format away from the 2003 tree, where each proof has one
conclusion. Measured on xtext's English texts, read twice with and
without their classes, the role of a formula came from its class only
on 94 of 1933 lines: words were not enough even for texts written by a
program from a fixed vocabulary. The format was therefore changed, after
a written proposal (`proposal/PROPOSAL.md` in the repository). This is
the format described now, and the one the tools implement.

== The format now: the 2003 tree, two syntaxes <sec-v2>

A proof text has a header between two lines `---` (the Rocq libraries
to load, the default tactics, the language), a title `# name`, and then
the top node: the statement with its proof. The rules are these.

- *The tree of 2003.* A node has exactly one conclusion, any number of
  variables and hypotheses, which hold in the node and in its subnodes
  and nowhere else, facts and justifications, and its subnodes. Seen
  from outside, a node is the formula $forall V, H -> C$. A node sees
  the conclusions of the nodes before it in its list and before each
  node around it (the visibility rule of 2003).
- *Only what is tagged is used.* A formula's role is its class, written
  after it in Pandoc's attribute syntax (@tab-tags). An untagged formula
  and every word are plain text: shown, not used. A line with no tag at
  all is a _remark_: shown, not checked. In "A, that is B", B is the
  conclusion and A is plain text.
- *Justifications* are names in the sentence, emphasised and tagged like
  a formula: `By definition of and (*conj*{.just}), we have`. A node
  may have several (`Applying *i*{.just} to *k*{.just}`); 2003 had one
  `j` per proof. The word "by" is an ordinary word. Two justifications
  are fixed, `*match*{.just}` (a case analysis) and
  `*induction*{.just}`, possibly with the name of the type
  (`(*or*{.just}, *match*{.just})`); the meaning of any other word that
  is not a name is declared (@sec-words). A fact,
  #raw("`F`{.fact}"), must be a hypothesis or a conclusion the node can
  see.
- *Two syntaxes for the same tree*, which can be mixed at any depth. In
  the _structured_ syntax a list item is a node and its sub-items are its
  subnodes; a paragraph after the sub-items, indented as the item's
  text, belongs to the item, so that a conclusion can come after its
  subproofs. In the _free_ syntax a node is a Pandoc span `[…]{.p}`
  inside a paragraph, and spans nest; a node of several paragraphs is a
  div, `::: p` … `:::`. A list item is read as a span around its
  contents.
- *Open goals.* A conclusion tagged #raw("`C`{.goal}") is left open by
  the author (a proof in progress): it is not tried, and the nodes after
  it use it as any conclusion.

#figure(
  table(columns: 2, align: left, stroke: 0.4pt + luma(180), inset: 5pt,
    table.header([*2003*], [*the format now*]),
    [`<p>` a proof or a subproof], [a list item, a span `[…]{.p}` or a div `::: p`],
    [`<n>` a name], [the title `# name`; `(h)` after a hypothesis; `(n)` after a conclusion],
    [`<c>` the conclusion], [#raw("`C`{.claim}"), exactly one per node],
    [`<h>` an assumption], [#raw("`A`{.hyp}")],
    [`<v>` a variable], [#raw("`x y : T`{.var}")],
    [`<f>` a formula used], [#raw("`F`{.fact}"), a hypothesis or conclusion in scope],
    [`<j>` a justification], [`*X*{.just}`, one name each, any number per node],
    [(none)], [#raw("`C`{.goal}"), a conclusion left open],
  ),
  caption: [The tags of 2003 and their form in the format now.],
) <tab-tags>

@fig-syntaxes gives _praeclarum_ in both syntaxes. The free one
reproduces node for node the 2003 line
`<p><p> we have <c>x</c></p>, so <j>by <f>x -> z</f></j>, we get <c>z</c></p>`. cyp proves both texts,
and finds the same six nodes in each. @fig-render shows how they are
typeset (@sec-render).

#figure(
  {
    show raw: set text(size: 6.6pt)
    grid(columns: (1fr, 1fr), gutter: 8pt,
      raw(read("figures/praeclarum_tree.md").trim(), block: true, lang: "markdown"),
      raw(read("figures/praeclarum_free.md").trim(), block: true, lang: "markdown"),
    )
  },
  kind: image,
  caption: [_praeclarum_ in the structured syntax (left) and in the free
  syntax (right). "Altogether ..." is the closing paragraph of the item
  "Suppose ...". The step "We get `z` by `x -> z`" has the fact `x -> z`
  and one subnode, the step "we have `x`".],
) <fig-syntaxes>

There is no backward phrase any more: going backwards is nesting, as
the conclusion of a node follows from its subnodes. The reader reports
the errors of the tree at their node and line: a node with tags but no
conclusion, or with two; a name out of scope or given twice; an unknown
class; an unclosed span or div. Two more errors need the meaning of the
names and are cyp's: a justification that names nothing known, and a fact
that is no hypothesis or conclusion in scope.

One limit is known: Pandoc has no attributes on emphasis, so a Markdown
preview shows `*conj*{.just}` with its `{.just}`. prooftext reads
Markdown itself, so the PDF and the web page are not affected. The old
form `*by X*` is still read as the justification X.

The change touched every text. Counted before it on the 82 English
texts of xtext (1201 list items): 179 items named a justification with
`*by X*`, 124 items had hypotheses but no claim, 141 had both a claim and
a fact, and 384 had facts only, 321 of them "The element `z` belongs to
`E`", whose "facts" were not formulas. xtext now writes the tree
(@sec-xtext), and cyp's examples were tagged again.

= Reading and checking: cyp <sec-cyp>

== The text as a verification condition generator

cyp is a Rocq-Elpi command, `CypFile "proof.md".` A small OCaml driver,
the program `cyp`, writes the Rocq file that loads the libraries of the
header and runs the command. The command reads the Markdown into its
tree (prooftext's reader), elaborates each formula in the context of its
node (with `coq.parse.argument`), and builds one condition per node. The
conditions are numbered like the nodes, in Dewey notation: `1.1` is the
first subnode of node 1, and `0` is the top node, the statement.
@fig-conditions shows two of the six conditions of _praeclarum_, as
printed by `cyp --conditions`, beside a 2003 lemma for the paper's
`exp_pos`. The structure is the same: the context of a condition holds
the variables and hypotheses in scope, the conclusions of its subnodes
and those of the nodes before it. The difference is that the 2003
lemmas ended with `Apply ok`, and cyp tries to prove its conditions.

#figure(
  grid(columns: (1fr, 1fr), gutter: 10pt,
    // conditions 1.1 and 0 of figures/praeclarum.conditions.txt, the four
    // variable lines merged into one
    raw("  x y z t : Prop
  H1 : x -> z
  H2 : y -> t
  H3 : x /\\ y
  c1_1_1 : x
  ============================
  z

  ...
  H1 : x -> z
  H2 : y -> t
  c1 : x /\\ y -> z /\\ t
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
  caption: [Left: conditions 1.1 and 0 of _praeclarum_ in the structured
  syntax (output of `cyp --conditions`, the four variable lines merged
  into one). Condition 1.1 sees its subnode 1.1.1; condition 0 sees node
  1 generalised over its hypothesis. The hypotheses of the statement have
  no name in the text, so cyp names them `H1`, `H2`, `H3`. Right: a lemma
  generated in 2003, from the appendix of @thery2004colouring.],
) <fig-conditions>

cyp builds the proof term itself. A node is a function of its variables
and hypotheses, and each subnode is given once, as $forall V, H -> C$,
to the proof of what follows. The term is then type-checked by Rocq and
the lemma is defined, so `Print Assumptions` shows only the axioms of the
libraries used. A first version built one copy of a scope's proof per
claim, and the term grew quickly with the nesting: on a test of 12
nested steps of two claims, type-checking and definition took 31.7 s and
12.1 s, against 37 ms and 35 ms once each proof was given once. With the
tree, the test of 13 nested nodes in the repository type-checks in 35 ms
and is defined in 27 ms (figures of cyp's documentation).

== How a condition is closed

A condition is tried, in order, with:

+ the justifications of its node. A declared word (@sec-words), or one
  of the fixed `match` and `induction`, chooses the method; several are
  tried in turn. The other names (hypotheses, nodes, variables, lemmas)
  are handed to the method: put first in the context, a lemma added to
  it. With no declared word, the names are applied one after the other,
  as lemmas, and their premises closed by the other names, the rules and
  the default tactics. The facts of the node are put first too;
+ the rules of the proof. A rule is an Elpi clause in a file named in
  the header, for instance
  ```
  justify {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat }}).
  ```
  which applies a monotonicity lemma to a goal of that shape. This is
  where the knowledge of a field goes: rules are written once per field,
  not in cyp. A rule may also have a name, and once that name is
  declared as a word, a step justified by `*monotonicity*{.just}` is
  closed by those rules and no other;
+ the default tactics of the header (`by: lia | nia`), then cyp's own,
  and once more on the goal with its head unfolded. For the name `tauto`
  cyp runs itauto @besson2021itauto, because `tauto` can run for minutes
  on small goals that itauto closes at once. For `firstorder` it runs a
  bounded search: the unbounded tactic took more than 30 s and 7 GB of
  memory on one step of a text. No tactic is run on a goal with an
  existential variable;
+ a last, coarse _gap tactic_: a few bounded searches (taking the goal
  and hypotheses apart in at most 200 steps, then a search of depth 4 or
  `congruence`, case analysis on booleans or on a variable, induction on
  a binder of the goal, a constructor). A condition it cannot close
  costs at most 0.06 s (measured). On the conditions that the steps
  before left open in xtext's texts, it closed 99%. It is not tried on a
  step justified by named rules.

A conclusion that does not hold is still used by the nodes after it, as
on paper. A wrong step therefore makes the next steps easier, and the
red step is the one to look at first.

== Justification words <sec-words>

What a justification word means is written in the files of the proof,
not hidden in cyp. A Rocq command declares it, either as an Ltac
tactic or as the named rules of that word:
```
Ltac easy_check := lra.
CypJustification "checked" := easy_check.
CypJustification "monotonicity" := rules.
```
A word is declared once (a second declaration is an error that gives
the place of the first), and the declaration can be in a rule file of
the header, in a library of the `require` line, or, for `Cyp Lemma`, in
the `.v` file itself. The tactics that every text may name (`lia`,
`tauto`, `firstorder`, `arith`, ...) are declared the same way at the
end of cyp's library, so that every word has a visible declaration. A
word `X` is looked up in this order: `match` and `induction`; a name of
the text in scope (a hypothesis, a node, a variable), as a local name
hides a global one in Rocq; a declared word; a lemma. A word that is
none of these is an error of its node, whose message says how to
declare it. cyp's JSON output gives, for each declared word that a text
uses, the file and line of its declaration, and with `pdf.sh --source-root`
the PDF and the web page link the word to it.

== Bounds instead of time limits

cyp has no time limit: a time limit makes the verdict depend on the
machine and on its load. Every search it runs has a fixed bound instead,
or is a decision procedure that ends: `tauto` is itauto, whose leaf
tactic `auto` has depth 5, as `auto` itself; `firstorder` is the bounded
search above; `congruence`, `ring` and `lra` end. Two have no bound in
Rocq 9.1: Rocq's reduction, and `lia` and `nia`, whose depth options
are not read by the search. cyp runs them behind `lia_guard`, a check of
the goal's shape with no search: it refuses a goal with more than 50
case splits (disjunctions, `-`, `max`, `div`, ...) or more than 16
hypotheses. The thresholds are about 1.5 and 2 times the largest call
that succeeded among the 2873 calls measured (cyp on its examples and on
xtext's texts, xtext, and the search for the gap tactic); none of these
calls is refused. The guard bounds what `lia` is given, not its search.
The word `arith` runs `lia` (guarded), then `tauto`.

== The result, and the conditions left to the user

cyp writes the text back with a status at the start of each node (✅
proved, ❌ not proved, ▫️ a remark, nothing to check), and under a failing
node a folded block with the goal and Rocq's message. In the free
syntax the mark goes inside the span:
#block(raw(lines("figures/praeclarum_free.checked.md", 8, 9), block: true))
It also writes a JSON file that a VS Code extension (about 130 lines of
JavaScript) uses to colour the formulas by role and to show the goal of
a failing node on hover. The program `cyp` exits with 0 when the lemma
is defined (every node proved), 1 when it is not, and 2 when it cannot
run.

cyp is not a yes-or-no check: what it proves is proved, and the rest is
left as goals. An error of a node (a justification that names nothing,
a fact not in scope, two conclusions, a formula that does not parse) is
reported at the node, and the check goes on: the node is not tried, and
the nodes after it use its conclusion all the same. Inside Rocq,
`Cyp File "proof.md".` followed by `Proof. ... CypQed.` always succeeds. Each
condition left open, each open goal of the text, and the conclusion of
each node with an error, is a goal named after its number (`?c2` for 2, `?c2_1` for 2.1), which the
script proves by name with Rocq's goal selectors:

```
Cyp File "vc_file.md".
Proof.
  [c2]: apply Z.sqrt_nonneg.
  [c1]: apply Z.sqrt_nonneg.
CypQed.
```

The node is then marked 🔶 with its number. The command fails only when
the statement itself cannot be read, or on an error of Rocq outside cyp
(a library that is not found). The same proof can also be written as a
Rocq command, `Cyp Lemma`, whose statement is an ordinary lemma
statement and whose body is a list of nodes, each a list of words and
Rocq terms, a term followed by its class (`"{.claim}"`) and the list of
its subnodes; `Cyp Lemma` succeeds in the same way. A text may be written
in any language: cyp reads only the tags.

= Writing: xtext <sec-xtext>

`ExtractText foo.` prints the proof of the constant `foo` as a text. It
follows the basic transducer of @coscoy1995extracting, extended to
inductive types after Coscoy's thesis @coscoy2000thesis. Proofs ending
with `Qed` work too, since Rocq-Elpi gives the body of opaque constants.
The text has one list item per step, and names the lemma or rule used
by each step. It is meant to be faithful, not fluent: rewriting it into
prose is left to a later pass, by hand or by a language model.

```
ExtractText foo.                     (* prints the text, plainly *)
ExtractText foo in "fr".             (* in French; also it de nl ru zh ar ko la *)
#[tags] ExtractText foo.             (* prints it in the format of proof texts *)
ExtractText foo to "foo.md".         (* writes it to a file, in that format *)
ExtractText foo to "foo.typ".        (* in Typst, for a PDF *)
ExtractText_partial.                 (* inside a proof: the proof so far; ends it *)
```

The printed text is for a reader: the formulas in Rocq syntax without
backticks, no classes, no header and no title. The file, and the text
printed with the attribute `#[tags]`, are in the format of
@sec-format: the form that cyp and the Typst writer read. Both are
written by the same writer, the markup being a parameter.
`ExtractText_partial` writes a proof in progress, each open goal as a
step "Prove G" (#raw("`G`{.goal}") in the format, which cyp leaves
open), and ends the proof as `Abort` does. Like cyp, xtext has no time
limit: the tactics it tries, to check a contraction or to close a
subproof built by a tactic, are the bounded ones that cyp runs for the
same names, so a text does not depend on the speed of the machine. A
step closed in this way whose conclusion is arithmetic (an equality, an
order or `<>` on `nat`, `Z`, `N` or `R`) is justified by the word
`arith`.

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
  conversion step disappears. This guard is the thesis's, syntactic. The
  older direct translation, still available, adds a guard of its own:
  a merged step must still be closed by one of cyp's tactics, which then
  justifies it, so that cyp can check the text. With another switch this stage is the
  _selection_ of type annotations of the thesis (4.3.1), followed by the
  naming of intermediate results (4.3.2–4.3.3): each subproof used in an
  application becomes a step of its own, named P1, P2, ..., before the
  step that uses it.
+ *Writing*. A conclusion says the type it proves, then "that is" the
  required type when they differ. Every node is then given its
  conclusion: a line that only introduces variables or hypotheses is
  merged with its only sub-item, or its last sub-item becomes its
  closing paragraph.

The forms that the thesis treats in its chapter 6 (eliminations,
introductions, rewriting, `fix`) are written directly, and their
subproofs come back to the stages. Elimination and introduction theorems
are recognised by their type, not their name; an elimination is
justified by the fixed word, `match` or `induction`, and the name of
the type. The motive of a dependent
elimination is left out when Rocq's `elim` would find it again (thesis
6.4.1). A subproof built by a tactic is one step justified by the tactic
(thesis 5.4). @tab-sizes gives the sizes of the texts with each choice of
the second stage, on the 73 texts that are not proofs in progress.

#figure(
  table(columns: 3, align: (left, right, right), stroke: 0.4pt + luma(180), inset: 5pt,
    table.header([*second stage*], [*list items*], [*characters*]),
    [contraction none], [1414], [205 233],
    [contraction maximal], [872], [106 023],
    [contraction guarded (default)], [905], [113 547],
    [selection (thesis 4.3.1)], [981], [112 964],
  ),
  caption: [Sizes of 73 texts written by xtext with each second stage.
  The contractions were measured again in the tree format, with no time
  limit (2026-11-23); the selection was measured with the format used
  before the tree, and not again.],
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
and `ExtractText praeclarum.` prints
#block({
  show raw: set text(size: 7pt)
  raw(lines("figures/xtexts.out", 0, 9), block: true)
})
With `#[tags]`, or written to a file, the same text has its header, its
title and its tags; @fig-xtext shows it typeset. Each formula that cyp
uses carries its role, and the names that justify a step are tagged
where the sentence names them: the type `and` with the fixed `match` of
a case analysis, the hypotheses `h1`, `i`, `k`, the constructor `conj`. The line "Assume `x`
(k) and `y` (l)" has no conclusion of its own, so its last sub-item
became its closing paragraph ("So by definition of and ..."). cyp proves
this text in full.

#figure(
  image("figures/fig-xtext.png", width: 92%),
  caption: [xtext's _praeclarum_ in the format of proof texts, typeset by
  prooftext. The justifications are purple; each use of `h1`, `i`, ...
  links back to the place where the name is introduced.],
) <fig-xtext>

Stopped in the middle of the proof of the same statement, after `split`
and the first conjunct, `ExtractText_partial.` prints the proof so far,
with the open goal as a step:
#block({
  show raw: set text(size: 7pt)
  raw(lines("figures/xtexts.out", 29, 38), block: true)
})

= Shared libraries and languages <sec-shared>

cyp and xtext do not depend on each other. What they must agree on is in
two libraries.

- *prooftext* holds the reader of a text into its tree of nodes, in both
  syntaxes (with the places of its lines, for error messages), what each
  node says and the errors of the tree, the document of a writer and its
  writing, the header and its fields, the roles and how a formula
  carries its role, the justifications, fresh names, the tactics a text
  may name, and the marks of a checked text. A writer and a reader that
  disagree on a detail is the first thing that goes wrong when two tools
  share a format; here there is one reader, and a test reads back what
  the writer writes.
- The *lexicon* holds, per language, the phrases of the writer (the
  phrase that introduces a hypothesis, a conclusion, a case...) and the
  words of the legend. cyp no longer reads it: no word gives a role. The
  Typst writer uses it to tell a word from a name, so that the French
  "a" is never taken for a hypothesis `(a)`.

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
  caption: [xtext's _praeclarum_ in Arabic (written by
  `ExtractText praeclarum to "praeclarum_ar.md" in "ar".`), as typeset by prooftext. The formulas and
  the names stay left to right.],
) <fig-ar>

All of this is Elpi code loaded by Rocq: 1314 lines for cyp's checker,
3016 for xtext, 2712 for prooftext (including the reader of the tree,
the printer of formulas and the Typst writer) and 1013 for the lexicon
(the `.elpi` files, counted with `wc -l`, comments included).

= Rendering <sec-render>

== PDF and web page

A proof text is typeset with Typst @typst. The Typst writer is in Elpi,
next to the reader: it writes the tree that the reader gives, so a
Markdown text (written by xtext, checked by cyp, or written by hand, in
either syntax) is shown as it is written, and a text that xtext has just
built goes through the same path. The look is a Typst template, in one
place. A web page is made from the same Typst source with Typst's HTML
export (experimental in Typst 0.15); its formulas are MathML.

A structured text keeps its list: each item a paragraph with its bullet,
indented by its depth, and the closing paragraph after the sub-items. A
free text shows no structure in the PDF: its paragraphs are those the
author wrote, with the colours of the roles only. Margin bars and
corners around the nodes were tried in the proposal and left out: bars
mislead when several nodes share a line, and corners pile up at the end
of nested nodes. On the web page, the structure of a free text is shown
on demand: under the pointer, a node's conclusion is framed, its
hypotheses dashed, its direct subnodes tinted blue, and the formulas its
justifications, names and facts point to are outlined. This hover is a
small script at the end of the page (about 40 lines); without
JavaScript the page is the same, without the hover. @fig-render shows
the three cases.

#figure(
  grid(columns: 1, gutter: 8pt,
    image("figures/fig-tree-checked.png", width: 88%),
    image("figures/fig-free.png", width: 88%),
    image("figures/fig-hover.png", width: 80%),
  ),
  kind: image, placement: auto,
  caption: [_praeclarum_ typeset by prooftext. Top: the structured text
  checked by cyp (PDF). Middle: the free text (PDF), which shows no
  structure. Bottom: the free text as a web page, the pointer on node
  1.1 ("we get $z$"): its conclusion framed, its subnode "We have $x$"
  tinted blue, the hypothesis that its fact repeats outlined in blue
  (screenshot of Chrome, the hover fixed by the address
  `#hover=1.1`). The legend of the web page has a switch per role and
  the button ↺.],
) <fig-render>

== Formulas as mathematics

A formula is a Rocq string. For the PDF it is elaborated in Rocq, after
the `require` line of the text, then printed as a tree of mathematical
notation (operators with their levels, fractions, powers, roots,
delimiters, quantifiers grouped by type), then written as Typst maths. A
table, extensible by a library with Elpi clauses, gives the notation of
each constant: `Rdiv` is a fraction, `Rabs` is $|dot|$, `Datatypes.nat`
is $NN$. Before the change of format, on the 79 texts of xtext and the 8
of cyp's examples then available (2090 formulas), 2 formulas could not be
elaborated and were shown as code (variables bound by a `fix` that no
`Let` declares); this was not measured again. Every formula of the
figures of this note is mathematics. @fig-maths shows a text on real
numbers checked by cyp.

#figure(
  image("figures/fig-sqrt-square.png", width: 92%),
  caption: [A text of cyp's examples on real numbers, checked by cyp and
  typeset. The word _value_ is linked because it is also the name of a
  constant of Rocq's corelib: a known limit of the links.],
) <fig-maths>

== Roles, statuses and links

The role of a formula is a light background behind black text: sky
blue for variables, orange for hypotheses, yellow for conclusions, grey
for facts, and a reddish purple (`#d9a9cb`) for the name of a
justification. They are light tints of the Okabe–Ito palette, with no
red–green pair. We checked the pages under simulations of protanopia,
deuteranopia and tritanopia @machado2009cvd: the roles stay distinct.
Since colour alone is not enough, the legend at the end of a text also
gives each role a mark that needs no colour (a dashed line, a frame, a
dotted line). A checked text has a mark per node in place of the bullet
(✔ proved, ✘ not proved, ◆ left to a Proof block or an open goal, whose
formula is framed, ▫ nothing to check), cyp's message in a box under a failing node, and the node numbers in the
margin, as cyp numbers its conditions (@fig-drinker).

The roles can be turned off. In the web page each role of the legend is
a switch, a check box that turns the colour of that role on and off in
the whole text (style sheet only, no script), and the button ↺ puts every
switch back as the page started (a form's reset). For the PDF,
`pdf.sh --roles claim,just` colours only the roles listed; the web page then
starts with only their switches on.

The PDF and the web page have links. A name given to a hypothesis,
`(h)`, labels its node, and its later uses link back to it. A lemma
that Rocq locates in the corelib or the stdlib links to its entry in
the online documentation. With `pdf.sh --source-root`, a declared justification word links to the
file and line of its declaration (@sec-words).

== Where to find it

A gallery of every text of the repository, with their PDFs and web
pages, is published at #link("https://thery.github.io/coq_tmp/txt/")
(388 texts in its last build, of 2026-11-19, in the tree format; it is
older than the word `arith`). A tutorial, `cyp/TUTORIAL.md` and
`TUTORIAL-2.md`, goes from a first proof to the Rocq commands in
thirteen small examples, each a file whose output a script checks
again, so that the tutorial stays true. The same tutorial is one Rocq
file, `cyp/tutorial/tutorial.v`, each proof a `Cyp Lemma`, which can be
stepped through in the browser with rocq-web, a build of Rocq that runs
in the browser (#link("https://thery.github.io/rocq-web/")). rocq-web
also has a demo of xtext (`ExtractText`, in English or French, with
its tags, on a proof in progress) and one of cyp (`Cyp Lemma` and
`CypFile`, a wrong node left as the goal `?c1`).

= Experience <sec-experience>

== xtext's texts checked by cyp

The texts written by xtext carry the role of every formula and the
justifications of every step, so cyp can check them. This is a test of
both tools: it fails when xtext writes a wrong formula, a wrong role or a
wrong scope, and when cyp reads one wrongly. Each text is checked alone,
with at most 8 GB of memory and no time limit. @tab-results gives the results
stored in the repository (`xtext/cyp-check/results.tsv` and
`results_langs.tsv`, runs of 2026-11-23), with those of the format used
before.

#figure(
  table(columns: (2.6fr, 0.8fr, 0.9fr, 1fr, 1.1fr, 1.2fr),
    align: (left, right, right, right, right, right),
    stroke: 0.4pt + luma(180), inset: 5pt,
    table.header([*set*], [*texts*], [*proved*], [*not proved*], [*not checked*], [*time*]),
    [English, now], [80], [650], [2], [279], [113 s],
    [English, before], [80], [666], [17], [504], [176 s],
    [English, direct translation, before], [72], [923], [23], [213], [595 s],
    [9 other languages, now], [108], [711], [0], [90], [156 s],
    [each other language, before], [12], [77], [1], [38], [21–26 s],
  ),
  caption: [cyp on the texts of xtext. "Now" is the tree format;
  "before" is the format with roles from words and `*by X*`. Counts are
  list items (now: nodes). Not checked: before, the steps with no claim
  (_Let_, _Assume_, the announcement of a case analysis); now, the
  remarks, all of them lines "The element `t` belongs to `T`". The
  direct translation (not the default) was not run again; it had 5
  timeouts; the runs now have no time limit, and every text ends. Not
  counted now: the 6 open goals (◆) of the four English proofs in
  progress, which cyp does not try. Times are the sums over the texts.],
) <tab-results>

On the 80 English texts, cyp now proves 650 of the 652 nodes it tries.
The first runs of the tree gave 684 of 686; no node was lost since. The
6 open goals of the proofs in progress, easy and proved then, are now
left open, as their author meant; and with no time limit xtext proves
`std_andb_assoc`, a case analysis on three booleans in 29 nodes, in one
step by `tauto`. 16 of the 17 steps not proved before are proved: the sentences named the
lemma they come from ("Applying not_all_ex_not to A, P and H"), but only
as plain text, and the default tactics did not find it; the name is now
a justification, and cyp applies it. The drinker's paradox, @fig-drinker,
is one of them. The two nodes not proved are these. In `half_le`, a node
made of the binders of `lia`'s internal proof and its closing step
"Applying `ZMicromega.ZTautoChecker_sound`", not proved before either. In
`std_Nat_le_trans`, a step of setoid rewriting "By application, we have
`Morphisms.respectful iff iff (...)`, that is
`forall x y : Prop, x <-> y -> ...`": its conclusion is now the second form, which needs
`respectful` unfolded in a hypothesis, and the default tactics do not do
it. This is the one status that got worse. In the nine other languages,
each language gives 79 nodes proved and none not proved, and text by
text the counts are those of English.

#figure(
  image("figures/fig-drinker-checked.png", width: 96%),
  caption: [The drinker's paradox: the text written by xtext from a
  proof by `destruct`, `exists` and a classical lemma, checked by cyp
  (run again for this note) and typeset. Every node is proved; 1.1 is a
  remark.],
) <fig-drinker>

These results say less than they seem. cyp proves each node with its
justifications when they apply, and otherwise with its own tactics; a
green node means that the conclusion follows from its context, not that
it follows the way the sentence says. Making the text the actual proof
would need cyp to use the named justification and nothing else, as it
already does for a word declared as rules.

== What the measurements changed

Several choices came from measurements rather than from design.

- *Bounded tactics.* Unbounded `firstorder` caused most of the timeouts
  and memory blow-ups on xtext's texts, and `tauto` ran for minutes on
  a goal two hypotheses long. cyp now first checks whether a goal is one
  of its hypotheses, runs itauto for `tauto`, and bounds `firstorder`.
  With these bounds the time limits could go, in cyp and in xtext;
  the thresholds of `lia_guard` were set from the calls measured.
- *The gap tactic.* Its searches were chosen in a greedy order over the
  conditions left open by the English texts, each candidate tried on
  each open condition.
- *Tags or words.* The 94 lines of 1933 where words were not enough
  (@sec-format) were one of the reasons to use tags only.
- *Justifications.* Tagging the names that the sentences already gave
  proved 16 of the 17 steps that the English texts left open.

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
step that is not proved is reported and left as a goal rather than
rejected.

*Controlled natural language.* Naproche @cramer2010naproche checks
mathematical texts written in a controlled natural language, with
automated provers for the steps. Verbose Lean @massot2024verbose gives
Lean tactics in a controlled natural language, in English and French,
for teaching. In both, the words are the syntax. In cyp, the words are
free and only the marks count.

= Conclusion and future work <sec-conclusion>

The idea of 2003 survives the change of tools. A proof written as text,
with marked formulas, gives conditions that a prover can discharge, and
today's automation discharges most of the small ones. Writing such
texts from proof terms, and checking them with the same format, is a
cheap test of both directions. Going back to the tree of 2003, with
tags only, proved more of the steps of xtext's texts.

What remains, in order:

- make cyp use the named justification of a node and nothing else, so
  that a proved node follows for the reason given;
- the two nodes of xtext's texts that cyp does not prove;
- rebuild the published gallery, last built before the word `arith`;
- the parts of the paper and the thesis that xtext does not implement:
  the "further optimisations" of @coscoy1995extracting, the specific
  wordings for connectives and classical reasoning, the scripts of the
  thesis's chapter 4, mutual fixpoints;
- a review of the phrases of each language by native speakers;
- turning xtext's faithful texts into fluent prose while keeping them
  checkable, which the format makes possible: a rewritten text is checked
  again by cyp, and the free syntax lets it be ordinary paragraphs.

The code is in the repository `coq_tmp` (directories `cyp`, `xtext`,
`prooftext` and `lexicon`; the design of the format in `proposal`).

#bibliography("refs.bib", style: "springer-basic-author-date", title: "References")
