# A format for proof texts: the 2006 tree, two ways to write it

Status: a proposal.  Nothing in cyp, xtext or prooftext has changed.
The examples are hand-written, and so are the mock-ups (Typst and HTML).
No reader produced them.

Decisions already taken by the user, which this proposal follows:

1. cyp uses only what is tagged.  There is no guessing from keywords: an
   untagged formula is plain text and is not used.
2. A formula tagged as a fact is used by cyp.
3. A justification is coloured inside the sentence.  It is an emphasised
   name: "By definition of and (*conj*), we have …".
4. The structure of the 2006 paper comes back: one conclusion per proof
   node, subproofs, and scopes for hypotheses and variables.
5. The question this proposal answers: can a free syntax and a
   structured syntax live together without a mess?  Yes, if both are
   two ways of writing the same tree, read by one reader.

## 1. The tree (the paper's grammar)

The 2006 paper (§2.2) has seven tags: `p` proof, `c` conclusion, `h`
hypothesis, `v` variable, `n` name, `f` formula, `j` justification.  Its
grammar, written here as the tree a reader builds:

```
text  ::= header, title (the name n of the top node), node
node  ::= one conclusion c            exactly one
          at most one name n          the name of the node, used by later justifications
          one justification j          the union of all its names and facts (may be empty)
          variables v*                 in scope in the node and its subnodes
          hypotheses h*                each: a formula, at most one name
          subnodes node*               in the order of the text
j     ::= (name | fact)*               a name: a hypothesis, a node, a lemma, a rule, a tactic
                                       a fact: a formula (the paper's <f> in a <j>)
```

The order of the parts inside a node is free.  The conclusion may come
first ("We prove C: …", goal-directed) or last ("…, so we get C",
forward), as in the paper.

The top node is the statement together with the proof.  The statement
gives the top node's variables, hypotheses and conclusion.  The top-level
steps are its subnodes.

### The tags, in Markdown

| paper | Markdown (both syntaxes) |
|---|---|
| `<p>` | a list item (structured syntax), or a span `[…]{.p}` (free syntax) |
| `<c>` | `` `F`{.claim} `` |
| `<h>` | `` `F`{.hyp} ``, with its name after it: `` `F`{.hyp} (h1) `` |
| `<v>` | `` `x y : T`{.var} `` |
| `<n>` of a node | `(name)` right after the node's conclusion |
| `<j>` holding a name | the name emphasised: `*conj*`, `*h1*`, `*Nat.add_comm*` |
| `<f>` in a `<j>` | `` `F`{.fact} `` |

**Justification.**  Emphasised text that is a single name is a
justification.  A name is an identifier, possibly qualified (`h4`,
`and_ind`, `Nat.add_comm`, `Corelib.Init.Logic.conj`).  It is coloured
in purple in the PDF and the web page (the role `by` of the template,
on main since 76b314b), and cyp uses it.  Emphasis on anything else
(several words, a formula) is plain emphasis.  The word "by" is an
ordinary word of the sentence:

```markdown
By definition of and (*conj*), we have `z /\ t`{.claim}.
By *h4* we have `A`{.claim}.
Applying *i* to *k*, we have `z`{.claim}.
```

A node may hold several names ("Applying *i* to *k*").  Together they
are its one justification, as in the paper, where a `<j>` holds several
names.  Today's `*by X*` is still accepted, as the name X.

**Fact.**  `` `F`{.fact} `` is a formula the node uses, the paper's `<f>`
inside a `<j>`.  It must be a hypothesis or a conclusion that the node
can see (section 4).  Example from the paper: "From `0 < a < b`{.fact} we
have `0 < b + a /\ 0 < b - a`{.claim}".

An untagged formula is plain text.  It is shown, without colour, and cyp
does not use it ("By *h2* we have `Inv E R y z`, that is `R z y`{.claim}").

## 2. Syntax (a): structured

A list item is a node; its sub-items are its subnodes.

```markdown
- Suppose `x /\ y`{.hyp}.
  - We get `z`{.claim} by `x -> z`{.fact}, since
    - we have `x`{.claim}.
  - We get `t`{.claim} by `y -> t`{.fact}, since
    - we have `y`{.claim}.

  Altogether we have `z /\ t`{.claim}.
```

How the reader builds the tree:

- the text of an item, up to its first sub-item, belongs to the item's
  node;
- each sub-item opens a subnode, in order;
- **the closing paragraph**: a paragraph after the sub-items, indented
  as the item's text (here "Altogether …"), belongs to the item's node
  too.  This is plain Markdown (a list item may hold a paragraph after
  its sub-list; Pandoc reads it so).  It lets a node give its conclusion
  after its subproofs, the forward style of the paper.  Today's reader
  does not accept it;
- the parts (`{.claim}`, `{.hyp}`, `{.var}`, `{.fact}`, `*name*`,
  `(name)`) found in that text go to that node.

There are no backward keywords any more (*it suffices*, *equivalent to
prove*).  Going backwards is nesting: a node's conclusion follows from
its subnodes (square_pos below).

## 3. Syntax (b): free prose

A node is a Pandoc span `[…]{.p}` inside a paragraph.  Spans nest.  The
marks `[`, `]{.p}` never show.

```markdown
[Suppose `x /\ y`{.hyp}. [[We have `x`{.claim}]{.p}, so by `x -> z`{.fact}
we get `z`{.claim}.]{.p} [[We have `y`{.claim}]{.p}, so by `y -> t`{.fact}
we get `t`{.claim}.]{.p} Altogether we have `z /\ t`{.claim}.]{.p}
```

How the reader builds the tree:

- everything after the title is the top node;
- each `[…]{.p}` opens a subnode of the innermost node around it;
- each part goes to the innermost node around it;
- a span cannot cross a paragraph (a Pandoc rule).  A subproof of several
  paragraphs is a fenced div, `::: p` … `:::`, which nests like a span.

Pandoc 3 reads the five free examples as nested spans exactly as above
(checked with `pandoc -t native`).  prooftext's reader is its own (it
does not use Pandoc), so it has to parse brackets: a `]` inside a
formula's backticks does not count.

## 4. One reader for both, and mixing

A list item is an implicit `[…]{.p}` around the item's text, its
sub-items and its closing paragraph.  So both syntaxes give the same
tree, and they can be mixed at any depth.  A list item may hold spans:

```markdown
- [We have `x`{.claim}]{.p}, so by `x -> z`{.fact} we get `z`{.claim}.
```

is one node (conclusion `z`) with one subnode (conclusion `x`).  This is
the paper's own line, `<p><p> we have <c>x</c></p>, so <j>by <f>x ->
z</f></j>, we get <c>z</c></p>`.  The structured syntax alone must put
`x` in a sub-item below (examples/praeclarum.structured.md).

Mixing does not cause a mess because the reader has one rule: a node is
opened by an item, a span or a div, and a part belongs to the innermost
open node.

## 5. Scope, and what each node proves

For a node P with variables V, hypotheses H, conclusion C, subnodes
P1 … Pk and justification J:

- **Scope.**  V and H are visible in P and in all its subnodes, and
  nowhere else.
- **Seen from outside.**  Outside P (from its parent, and from the
  siblings after it), P is the formula ∀ V, H → C.  This is the paper's
  `(c_p1 h1)` and today's cyp "local scope" rule.
- **The condition of P** (what cyp proves for P): C, in the context
  made of
  - the variables and hypotheses of P and of its ancestors;
  - the conclusions of P1 … Pk, each seen from outside;
  - the conclusions of the earlier siblings of P and of each of its
    ancestors, seen from outside (rule R1 below).

  J chooses how: a name runs as today (a rule, a lemma, a hypothesis,
  a tactic); a fact must be in this context.  With no J, the default
  tactics run, as today.

**Which earlier steps can a node use?**

- **R1, the paper's rule** (2006, end of §2.3): "the conclusion of p_i is
  visible inside p_j for i < j and invisible outside P".  Earlier siblings
  are visible, at every level.  This is what cyp does today ("each step
  from the claims of the steps before it").  xtext's texts rely on it:
  in Trans_Inv, the last top-level step uses the step before it.
- **R2, strict natural deduction**: siblings are independent.  A node
  sees only its ancestors' variables and hypotheses and its own
  subnodes.  Every forward chain of n steps becomes n levels of nesting.
  xtext would have to nest every step that uses an earlier sibling, and
  cyp's examples too.

Recommendation: R1.

**One conclusion per node** replaces today's "several claims per step,
each also from the claims before it".  Condition numbers become plain
Dewey numbers (`2.1`); there is no more `2a`, `2b`.

## 6. Errors

The reader stops on these, with the line and the node's number:

| error | example |
|---|---|
| a node with no conclusion (it has tags, but no `{.claim}`) | `- Assume `x`{.hyp} (k).` with sub-items but no closing paragraph |
| a node with two conclusions | `we have `A`{.claim}, hence `B`{.claim}` in one node |
| a name that names nothing known | `*h7*` with no h7 in scope, no lemma, rule or tactic h7 |
| a name that is out of scope | `*k*` used outside the node that assumes k |
| a fact that is no visible hypothesis or conclusion | `` `R x y`{.fact} `` when nothing in scope is `R x y` (up to conversion) |
| a name given twice in one scope | two hypotheses `(h)` both visible |
| a statement with no conclusion | the title is followed by no `{.claim}` |
| an unknown class | `` `F`{.clam} `` (today it is silently no role) |
| an unclosed span or div | `[… {.p}` with no `]`, a `::: p` with no `:::` |

## 7. How the PDF and the web page show it

The marks (`{.claim}`, `[`, `]{.p}`, `*`) never show.  Colours are on
formulas and justification names only, with no frames, as in today's
template: variable sky blue, hypothesis orange, conclusion yellow, fact
grey, justification name purple.  The legend has the five.

| | PDF | web page |
|---|---|---|
| structured | as today: a bullet and an indentation per depth; the closing paragraph at the indentation of its item's text | nested lists; the same hover as below |
| free | a paragraph; the structure is invisible (render/free-plain-1.png), or a thin bar in the left margin per depth (free-brackets-1.png), or small grey corners ⌜ ⌟ around each node (free-corners-1.png) | under the pointer, the node's conclusion is framed, its hypotheses dashed, its direct subproofs tinted blue; over a justification name, the hypothesis it names is outlined; over a fact, the formula it repeats |

What the mock-ups show plainly:

- margin bars give only line ranges.  When several nodes share a line
  (praeclarum, exp_pos), the reader cannot tell where each starts;
- corners are exact, but they pile up at the end of nested nodes
  (`⌟⌟⌟`);
- the hover needs a little JavaScript (about 30 lines).  Today's page
  needs none.

## 8. What changes for xtext's texts

Counted on the 82 English texts of `xtext/examples/` (1201 items):

| today | count | in the new format |
|---|---|---|
| items with `*by X*` | 179 | the name already in the sentence becomes emphasised ("By definition of and (*conj*)"); no separate `*by X*` (still accepted when read) |
| items with no claim, with hypotheses or variables ("Assume `x`{.hyp} (k) and `y`{.hyp} (l).") | 124 | a node must have a conclusion: merged with its only sub-item, or its last sub-item becomes its closing paragraph (choice 2) |
| items with a claim and a fact ("…`{.claim}`, that is `…`{.fact}") | 141, of which 49 "that is" | one conclusion: the form the next steps use is the claim; the other form is plain, or a fact when it is a hypothesis in scope (choice 3) |
| items with facts only, no claim | 384, of which 321 "The element `z`{.fact} belongs to `E`{.fact}" | a fact must be a known formula, and `z` is not one: these lines become plain (untagged), remarks (choice 5), or are left out |

The two xtext examples rewritten here (examples/xtext_praeclarum.*,
examples/Trans_Inv.*) show each case.  Today's versions are beside them
(`*.today.md`).

cyp's examples: 8 of the 10 in `cyp/examples/` have no `{.claim}` (they
rely on keywords), and 2 use backward keywords.  All 10 must be tagged,
and the backward ones nested.

## 9. Open choices

Each choice has a recommendation and a list of what it changes.

1. **Visibility: R1 (paper) or R2 (strict).**  Recommended: R1.
   Cost of R1: none beyond the tree (cyp already chains).  R2: xtext and
   cyp texts nest every chained step.
2. **A node with no conclusion** (124 xtext items).  (a) error; xtext
   merges an "Assume" item with its only sub-item, or turns its last
   sub-item into the closing paragraph; (b) the reader takes the
   conclusion of the last subnode.  Recommended: (a): the structure is
   then written, not inferred.  Cost: xtext writer (a generic rule on
   scope-only steps), its expected test outputs, regenerated examples.
   (b): a reader rule, no xtext change.
3. **Restatements "A, that is B"** (49 items).  Recommended: B is the
   claim, A plain (as in the examples here).  Alternative: A a fact when
   it is a hypothesis in scope (it is then checked, but repeats the
   name).  Cost: xtext writer only.
4. **A fact not found in scope.**  (a) error; (b) a condition of its own,
   proved like a claim before use.  Recommended: (a), as the paper's `<f>`
   names something known.  Cost: cyp looks the fact up (conversion);
   xtext stops tagging non-formulas as facts (the 321 "belongs to"
   lines).
5. **An item with no tag at all.**  (a) a remark: shown, not a node,
   not checked; (b) an error.  Recommended: (a), so that xtext can keep
   sentences like "The element `z` belongs to `E`" without tags.  Cost:
   one reader rule; the PDF may show remarks in grey.
6. **An emphasised single word that names nothing** ("this is *not*
   obvious").  (a) error "unknown name not"; (b) plain emphasis.
   Recommended: (a), as (b) is guessing; plain emphasis of one word is
   written `_not_`, which is never a justification.  Cost: the reader
   tells `*` from `_` (it reads the Markdown itself, so it can).
7. **Structure of a free text in the PDF**: none, margin bars or
   corners.  Recommended: none.  Bars mislead when nodes share a line,
   and corners are noisy.  An author who wants the structure visible on
   paper uses the structured syntax, or mixes it in.  Cost: none.  Bars:
   about 20 lines of Typst in the template (render/free-brackets-1.png).
8. **The hover on the web page.**  Recommended: yes, for both syntaxes.
   It is the only place where a free text shows its structure.  Cost:
   the template writes `class="p"` on nodes and adds a small script, so
   the page is no longer free of JavaScript.

What changes in each part, whatever the choices:

- **prooftext**: the tree (`document.elpi`: a node has a text, subnodes
  and a closing text; one conclusion); the reader (closing paragraph,
  nested `[…]{.p}` spans and `::: p` divs, `*name*`, the errors of
  section 6); the Typst writer and template (closing paragraph, `class="p"`,
  hover script if choice 8).  The `by` colour is already on main.
- **cyp**: remove the keyword roles (en, fr, it lists) and the backward
  keywords; build the conditions from the tree (section 5); look up
  facts; one claim per node; rewrite its 10 examples.
- **xtext**: write `*name*` instead of `*by X*`; one conclusion per node;
  the closing paragraph; choices 2-5; regenerate the 82 English texts
  and the translations (190 texts in all) and its expected outputs.
- **gallery**: regenerate; nothing else (the legend's justification is
  already on main).

## Files

- `examples/`: for each example, `NAME.2006.xml` (the paper's, unchanged)
  or `NAME.today.md` (xtext's today), `NAME.structured.md`,
  `NAME.free.md`.  Paper: praeclarum, square_pos, exp_pos (formulas as
  in 2006, not checked).  xtext: xtext_praeclarum, Trans_Inv.
- `mockup/`: `lib.typ` (mock-up functions over today's template),
  `structured.typ`, `free.typ`; `structured.src.html`, `free.src.html`
  (shorthand, expanded by `build-html.sh` with `expand.sed`, around
  `common-head.html` and `common-tail.html`), giving `structured.html`
  and `free.html`.
- `render/`: `structured.pdf`, `free-plain.pdf`, `free-brackets.pdf`,
  `free-corners.pdf` and their PNGs (`*-1.png`); `structured-html.png`,
  `free-html.png`; the hover, fixed by the address (headless Chrome
  cannot hover): `free-html-hover.png` (`free.html#hover=x1.1.1`),
  `free-html-by.png` (`#by=x1.1.1.1/i`), `structured-html-hover.png`.
- `render.sh`: makes all of `render/` (Typst 0.15, pdftoppm, Chrome).
