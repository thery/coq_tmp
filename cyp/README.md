# cyp: coloured proofs

A proof is written in Markdown, as on paper.  cyp turns each node of its tree into a
Rocq goal, tries to prove it, and writes the proof back in Markdown, with
✅ in front of each proved node and ❌ in front of the others; under a ❌, a
folded block gives the goal and Rocq's message, or the error.  When every
node is proved, the lemma is defined in Rocq.

cyp is written in Rocq-Elpi ([vernac/](vernac/README.md)): the command
`CypFile "proof.md".` reads the Markdown, checks it and writes the
result.  The program `cyp` ([bin/cyp.ml](bin/cyp.ml)) is only a driver:
it writes the small Rocq file that loads the proof's libraries and rules
and runs this command.

It needs the opam switch `elpi5` (Rocq 9.1.1, Elpi 4.0.0, rocq-elpi master
4a8efd9: `coq.parse.argument`, coq-elpi pull request #1133, and
`coq.ltac.name-uvar`, which names the goals of a Proof block), and
coq-itauto, which cyp runs for the name `tauto` (`tauto` may run for
minutes on small goals that itauto closes at once).  The released
coq-itauto 9.1.0 needs two fixes for Rocq 9, in the copy pinned in
`elpi5` (`~/git/itauto-rocq9`): its opam file depends on `rocq-core` and
`rocq-stdlib` instead of the `coq` meta-package (which would bring the
standard library down to 9.0.0), and its classical mode (`Itauto
Classic`, which cyp sets) looks for `Stdlib.Logic.Classical_Prop`, the
name of the classical library since Rocq 9:

```sh
dune build
(cd vernac && rocq c -Q . CypV -Q ../../lexicon Lexicon -Q ../../prooftext ProofText Gaps.v Cyp.v)   # the cyp library
export CYP_LIB=$PWD/vernac
dune exec cyp -- examples/square_pos.md   # writes square_pos.checked.md and square_pos.cyp.json
dune exec cyp -- --conditions examples/square_pos.md   # prints the conditions, tries nothing
```

## The format

The format of proof texts is prooftext's
([../prooftext/README.md](../prooftext/README.md#the-format)): the tree of
the 2003 paper, in Markdown.

```markdown
---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia | nia
---

# square_pos

Let `a b : Z`{.var}. If `0 < a < b`{.hyp} then `a * a < b * b`{.claim}.

- It is equivalent to prove `0 < b * b - a * a`{.claim}.
  - That can also be written as `0 < (b + a) * (b - a)`{.claim}.
    - From `0 < a < b`{.fact} we have `0 < b + a /\ 0 < b - a`{.claim}.
```

- **The header** (between the two `---`): `require`, the Rocq preamble;
  `scope`, a scope to open; `by`, the tactics tried on a node with no
  rule or tactic name; `rules`, files of rules (below), separated by
  spaces, copied in order after the preamble; `flags`, options given to
  `rocq c` (e.g. `-Q dir Name`; the directories of `-Q`, `-R`, `-I` and
  the rule files are relative to the directory of the proof, and
  `${NAME}` is the environment variable NAME, so that a proof does not
  name the directories of one machine); `lang`, the language of cyp's
  messages (`en`, `fr`, `it`; the text itself may be in any language);
  `gaps: off`, no gap tactic (below).  There is no time limit per node.
- **cyp uses only what is tagged.**  A formula's role is its class:
  `` `x y : T`{.var} `` (variables; `` `u := e`{.var} `` a local
  definition), `` `A`{.hyp} (h) `` (a hypothesis and its name; without a
  name, cyp names it with the first of `H1`, `H2`, ... that nothing in
  scope has, example `examples/unnamed_hyps.md`), `` `C`{.claim} (n) ``
  (the conclusion of the node and its name), `` `F`{.fact} `` (a fact the
  node uses), and `*X*{.just}` is a justification.  A formula with no
  class and every word are plain text: no word gives a role (the lexicon
  of xtext's writing is not read).  A tag is Pandoc's attribute syntax; it
  does not appear in the PDF or the web page.
- **A node** is a list item (its sub-items and its closing paragraph are
  its own), a span `[ ... ]{.p}` or a div `::: p` ... `:::`, mixed at any
  depth (prooftext's two syntaxes).  It has one conclusion.  An item with
  no tag at all is a remark: shown (▫️), not checked; its sub-items belong
  to the node around it.
- **What a node proves** (its *condition*): its conclusion C, from the
  variables and hypotheses of the node and of the nodes around it, from
  its subnodes, and from the nodes before it in its list and before each
  node around it (the paper's rule).  A node is known outside as ∀ V, H →
  C, its variables V and hypotheses H generalised, whatever its proof: a
  case of an induction is a node *Let `m`{.var}; assume `P m`{.hyp} (IH).*
  with its conclusion.  There are no backward words (*it suffices to
  prove*): going backwards is nesting (square_pos above).
- **A fact** `` `F`{.fact} `` must be a hypothesis or a conclusion that the
  node sees, up to conversion (a fact that is none is an error); the
  hypothesis it is, is put first for the proof of the node.
- **Justifications**, `*X*{.just}`, any number in a node, written where
  the sentence mentions them ("Applying *i*{.just} to *k*{.just}"):
  - a name of rules (`named`, below) or of a tactic (`lia`, `lra`, `nia`,
    `nra`, `ring`, `field`, `tauto`, `auto`, `easy`, `reflexivity`,
    `assumption`, `congruence`, `firstorder`, or one that the rules of the
    proof add with `tactic-name Name Ltac`) chooses the method; several are
    tried in turn.  `firstorder` is run bounded, as `bounded_firstorder` of
    [../prooftext/Tactics.v](../prooftext/Tactics.v), shared with xtext: the
    tactic itself has no bound (more than 30 s and 7 GB on one step of a
    text);
  - a name of a hypothesis, of a node (`n`, or `c2` for node 2 when it has
    none) or of a variable, or of a lemma (possibly qualified,
    `Nat.add_comm`) is handed to the method: put first in the context, a
    lemma added to it (Ltac `cyp_first`);
  - with no rule or tactic name, the names handed are applied one after
    the other, like a lemma, the premises that are one of the other names
    closed by it first, the others by the rules or the default tactics
    ("*and_ind*{.just} in *h1*{.just}"); a single `*X*{.just}` so means
    what `*by X*` meant;
  - with no justification, all the rules, then the tactics of `by`, then
    cyp's own (`tauto`, `lia`, `nia`, `lra`), the facts first;
  - a name that is none of these (and no name of the text in scope) is an
    error.  X cannot be tactic code (`interval with (i_prec 100)`):
    Rocq-Elpi cannot yet turn a string into a tactic; name an Ltac
    definition instead (`tactic-name`).
- **The transition.**  The texts written before the tree (xtext's, until
  they are written again) name a justification `*by X*`: it is read as
  `*X*{.just}`.
- **Errors** of the tree, reported at their node and line (in the checked
  Markdown and the JSON), and the node is not proved: a node with tags but
  no conclusion, two conclusions, a name out of scope or given twice in
  one scope, an unknown class, an unclosed span or div (prooftext's
  table); a fact that is no visible hypothesis or conclusion; a
  justification that names nothing known
  ([examples/errors_demo.md](examples/errors_demo.md)).  The subnodes of a
  node with an error are checked all the same.
- **The gap tactic.**  A condition that its justifications, the rules and
  the default tactics leave open gets a last, coarse try: `cyp_gap`
  ([vernac/Gaps.v](vernac/Gaps.v)), a few bounded searches (the goal and
  the hypotheses taken apart, then a proof search of depth 4 or
  `congruence`; a case analysis on the booleans; an induction on a binder
  of the goal; a case analysis on a variable; a constructor whose arguments
  the search finds), with no time limit: a condition it cannot close costs
  a bounded search (at most 0.06 s measured).  On the conditions cyp left
  open in xtext's texts (closing steps of case analyses and inductions,
  steps that follow from earlier claims by a few applications) it closed
  99% ([../xtext/gaps/](../xtext/gaps/README.md)).  It is not tried on a
  node justified by named rules (*monotonicity*{.just}: those rules only).
  The header line `gaps: off` turns it off
  ([examples/gaps_demo.md](examples/gaps_demo.md) is proved with it, not
  without).

A conclusion that does not hold makes the nodes after it easier to prove,
as on paper: a red node is the one to look at first.

**Conditions.**  The text is a verification condition generator: each
node gives one condition, numbered like the node (`2`, `2.1` for the first
subnode of node 2, `0` for the statement), which cyp discharges.  Inside
Rocq, the conditions it does not discharge can be left to a Proof block
of ordinary tactics, `Cyp File "proof.md". Proof. ... CypQed.` (marked 🔶
with their numbers), where each is a goal named after its node (`?c2` for
2, `?c2_1` for 2.1) and proved by `[c2]: tac.`, see
[vernac/](vernac/README.md).

**The checked Markdown** is the text itself, with the mark of each node's
status at the start of its own text (`- ✅ ...` for an item, `[✅ ...]{.p}`
for a span) and its message in a folded block after the paragraph where it
starts.  **The JSON** (`cyp --json`) gives, for each node, its number,
its first and last lines (numbered from 0), its status, its formulas and
its message.

## Rules: choosing the justification with Elpi

A field has its own way of proving things: products of nonnegative reals
are compared by a monotonicity lemma, rounding errors by a lemma of Flocq,
bounds by `interval`.  This knowledge goes in rule files named in the
header (`rules: float.elpi my_proof.elpi`), not in cyp.

The proved facts the rules use are ordinary Rocq lemmas, in a library the
proof loads in its `require:` field.  The rules themselves are Elpi
clauses, in files `.elpi`, added to the database `cyp.db` (defined in
[vernac/Cyp.v](vernac/Cyp.v)):

```elpi
% the product of nonnegative reals is monotone
justify {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat }}).
```

- `justify Pattern (apply T)`: on a goal that matches `Pattern`, apply
  the lemma `T`, its arguments found by unification, then close each
  premise with the rules, or else with the default tactics of the proof
  (its `by:` field).
- `justify Pattern (lemma T)`: the same with an explicit term `T`, holes
  written `_`.
- `justify Pattern (ltac "name")`: the Ltac tactic `name`, which must
  close the goal; for genuine tactics (`interval with ...`), not for an
  `apply`.
- `justify_first Pattern Tac`: a rule tried before every `justify` rule,
  for the rules of one proof that must win over shared ones.
- `named "name" Pattern Tac`: a rule with a name, tried like the others,
  and the only kind tried when a node is justified by `*name*{.just}`: the
  text says why a node holds (*monotonicity*{.just}), the rule file says what that means,
  and Rocq checks that this reason, and no other, closes the step
  ([examples/named_demo.md](examples/named_demo.md)).

A rule is an Elpi clause, so it may have a body, for example to fire only
when another rule applies.  On a node with no rule or tactic name, the rules are
tried in order, then the default tactics.  Conjunctions and disjunctions
are split by cyp itself.  A rule file may also be a `.v` file of Rocq
text, copied into the proof as it is.  The lemmas of a field go in a
compiled library, never in a file loaded with `Load`: a lemma proved by
`interval` in a loaded file keeps its numerical check as an assumption
(`Print Assumptions` lists it as an axiom).

Example: [examples/rules_demo.md](examples/rules_demo.md) with
[examples/rules_demo.elpi](examples/rules_demo.elpi) proves its three
nodes; without the rule file, `lra` proves only one.
A larger case study, a floating-point paper with a library of lemmas and
shared rules, is kept in a private branch.

## The PDF

```sh
../prooftext/pdf.sh examples/square_pos.checked.md   # square_pos.checked.typ, then square_pos.checked.pdf
```

makes the PDF of a checked text with Typst, in the template that
prooftext shares with xtext
([../prooftext](../prooftext/README.md#the-pdf-of-a-proof-text-typst)):
each step has its status as a coloured mark (✔ proved, ✘ not proved, ◆
left to a Proof block, ▫ nothing to check), cyp's message in a box under
it, and its number in the margin, the number of its conditions; the
legend at the end recalls the marks and the looks of the roles, and the
names (h) and the lemmas are links (to their steps, to their
documentation).  The
formulas have the style of their role when the text gives their class
(`{.claim}`, as xtext's texts do); a formula without a class is shown
without a role, as cyp reads it: plain text.  The marks of a checked text are prooftext's (`checked.elpi`), so
that the Typst writer reads back exactly what cyp writes.  The formulas are
mathematics (√x², fractions, |x|, ≤), printed from the terms they elaborate
to, as cyp reads them (`--code` keeps the Rocq code, `--html` makes an HTML
page): `examples/sqrt_square.md` is a text on real numbers that shows them.

## The editor

[vscode/](vscode) is a VS Code extension (plain JavaScript, nothing to
build): on saving a proof it runs `cyp --json`, colours each formula by
its role, marks each step with a green ✓ or a red ✗, and shows the goal and
Rocq's message of a failing step on hover.  Install it by linking the
directory into `~/.vscode/extensions/`; set `cyp.command` to the command
that runs cyp (for instance `opam exec --switch=elpi5 -- env
CYP_LIB=/path/to/cyp/vernac cyp`).

## Departures from the 2003 paper

cyp revives *Colouring proofs: a lightweight approach to adding formal
structure to proofs* (UITP 2003; ENTCS 103, 2004).  It keeps its tree: a
proof is a node with one conclusion, its hypotheses and variables
scoping over its subnodes, its justifications and facts; a node is used
from outside as ∀ V, H → C, and sees the nodes before it.  Each of the
seven tags of the paper (its section 2.2) has its Markdown form:

| paper (2003) | cyp |
|---|---|
| `<p>` a proof or a subproof | a list item, a span `[ ... ]{.p}`, or a div `::: p` |
| `<n>` a name | the title `# name`; `(h)` after a hypothesis; `(n)` after the conclusion of a node |
| `<c>` the conclusion | `` `F`{.claim} `` |
| `<h>` an assumption | `` `F`{.hyp} `` |
| `<v>` a local variable `name:type` | `` `x : T`{.var} `` |
| `<f>` a formula (a fact in a justification) | `` `F`{.fact} ``, checked to be a hypothesis or a conclusion in scope |
| `<j>` a justification, which holds names | `*X*{.just}`, one name each, any number per node |

The departures:

- Markdown instead of XML tags, so that a proof reads as a normal
  document, in two syntaxes for the same tree, structured (list items,
  with a closing paragraph after the sub-items) and free (spans and divs
  in the prose), mixed at any depth;
- several justifications per node, each one name, where the sentence
  mentions it (the paper has at most one `<j>` per `<p>`, which may hold
  several names); rule and tactic names choose the method, the other
  names are handed to it;
- remarks: a text with no tag is shown and not checked;
- the method of a node may also be chosen by Elpi rules from the shape
  of its goal, written per field in a rule file;
- under a failing node, its goal and Rocq's message, in the Markdown
  output and in the editor;
- the whole checker runs inside Rocq (Rocq-Elpi), and the same proof can
  also be written as a Rocq command, `Cyp Lemma` ([vernac/](vernac/README.md)).
