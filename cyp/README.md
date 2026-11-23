# cyp: coloured proofs

**New to cyp?**  Start with the tutorial, [TUTORIAL.md](TUTORIAL.md) and
[TUTORIAL-2.md](TUTORIAL-2.md): small checked examples, from a first proof
to the Rocq commands; also one Rocq file to step through in the browser
([rocq-web](https://thery.github.io/rocq-web/?example=cyp-tutorial&file=tutorial.v)).
This README is the reference.

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
  declared word (declared words: `lia | nia`); `rules`, files of rules (below), separated by
  spaces, copied in order after the preamble; `flags`, options given to
  `rocq c` (e.g. `-Q dir Name`; the directories of `-Q`, `-R`, `-I` and
  the rule files are relative to the directory of the proof, and
  `${NAME}` is the environment variable NAME, so that a proof does not
  name the directories of one machine); `lang`, the language of cyp's
  messages (`en`, `fr`, `it`; the text itself may be in any language);
  `gaps: off`, no gap tactic (below).  There is no time limit: what cyp
  proves never depends on time or on the machine, every search it runs has
  a fixed bound ([Deterministic bounds](#deterministic-bounds)).  A header
  line with any other key is ignored, and cyp says so (`cyp: the header
  line timeout: is ignored, timeout is no key of a header`: `timeout:`
  was a key of a draft of cyp).
- **cyp uses only what is tagged.**  A formula's role is its class:
  `` `x y : T`{.var} `` (variables; `` `u := e`{.var} `` a local
  definition), `` `A`{.hyp} (h) `` (a hypothesis and its name; without a
  name, cyp names it with the first of `H1`, `H2`, ... that nothing in
  scope has, example `examples/unnamed_hyps.md`), `` `C`{.claim} (n) ``
  (the conclusion of the node and its name), `` `C`{.goal} `` (the
  conclusion of a node that the author leaves to prove: an open goal,
  below), `` `F`{.fact} `` (a fact the
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
  the sentence mentions them ("Applying *i*{.just} to *k*{.just}").  What
  a word means is written in the files of the proof, never hidden in cyp:
  a word is a name of the text, of a lemma, or a word declared by
  `CypJustification` (below, "Declaring justification words").  A word X
  is looked up in this order:
  1. `match` and `induction`, the two fixed methods (below);
  2. a name of the text in scope: a hypothesis, a node (`n`, or `c2` for
     node 2 when it has none), a variable (the text's own names come
     first, as a local name hides a global one in Rocq);
  3. a word declared by `CypJustification "X" := ...`: an Ltac tactic or
     the rules named X;
  4. a lemma (possibly qualified, `Nat.add_comm`);
  5. else the node has an error, "X names nothing known ... (declare it:
     `CypJustification "X" := tactic.` or `:= rules.`)".

  What each kind does:
  - a declared word chooses the method; several are tried in turn.  The
    tactics that every proof text may name (`lia`, `lra`, `nia`, `nra`,
    `ring`, `field`, `tauto`, `auto`, `easy`, `reflexivity`, `assumption`,
    `congruence`, `firstorder`, `arith`: [../prooftext/tactics.elpi](../prooftext/tactics.elpi),
    the only ones xtext writes) are declared at the end of
    [vernac/Cyp.v](vernac/Cyp.v), each the Ltac `cyp_N` above them, with
    the same command.  `firstorder` is run bounded, as `bounded_firstorder` of
    [../prooftext/Tactics.v](../prooftext/Tactics.v), shared with xtext: the
    tactic itself has no bound (more than 30 s and 7 GB on one step of a
    text): the goal and its hypotheses taken apart, at most 200 steps, then
    a proof search of depth 4 or `congruence`;
    `arith` is `first [ guarded_lia | itauto auto ]` (`cyp_arith`), the word
    xtext gives to a step whose conclusion is arithmetic;
  - a name of a hypothesis, of a node or of a variable, or of a lemma is
    handed to the method: put first in the context, a lemma added to it
    (Ltac `cyp_first`);
  - the two fixed justifications state how the step eliminates an object,
    the way an author says it: `*match*{.just}`, a case analysis (Rocq's
    `destruct`, `cyp_match`), and `*induction*{.just}`, an induction
    (Rocq's `induction`, `cyp_induction`), on each hypothesis or variable
    the node names (else on the hypotheses its facts are), then each case
    closed by the rest of the node's method (its other names, the rules,
    the default tactics), the subnodes (the cases) in context: "By
    *induction*{.just} on *l*{.just}, we prove ...", "By case analysis
    (*match*{.just}) on *h*{.just}" ([examples/induction_demo.md](examples/induction_demo.md),
    [examples/cases_demo.md](examples/cases_demo.md)).  The name of an
    inductive type with them, `*or*{.just}`, says the type of the object:
    each object named must have it (else an error), and with no object
    named it is the one hypothesis or variable of that type in scope
    (none, or several: an error).  A type named without a method is an
    error ("*and* is an inductive type: it justifies a step only with
    *match* or *induction*").  `induction` is a name Rocq accepts for a
    lemma, but as a justification it is the method;
  - with no declared word, the names handed are applied one after
    the other, like a lemma, the premises that are one of the other names
    closed by it first, the others by the rules or the default tactics
    ("*and_ind*{.just} in *h1*{.just}"); a single `*X*{.just}` so means
    what `*by X*` meant; when none of them applies, the rules and the
    default tactics run, the names given first (a text may name the lemma
    a step comes from without its conclusion being the step's: "Applying
    *proj1*{.just}, we have `z`{.claim}", from `proj1 H1` applied to `x`);
  - with no justification, all the rules, then the tactics of `by`, then
    cyp's own (`tauto`, `lia`, `nia`, `lra`), the facts first; the tactics
    only on a goal with no existential variable (a premise of a lemma not
    yet determined: `firstorder` runs for very long on `z /\ ?B`), and at
    last, once, on the goal with its head unfolded (its weak head normal
    form: a conclusion `Inv E R x z`{.claim} that the steps before prove as
    `R z x`);
  - X cannot be tactic code (`interval with (i_prec 100)`): Rocq-Elpi
    cannot yet keep a tactic given as code; name an Ltac definition and
    declare a word for it (`CypJustification "bounds" := my_interval.`).
- **Open goals.**  A node whose conclusion is `` `C`{.goal} `` (a proof
  in progress: xtext's `ExtractText_partial` writes "Prove
  `C`{.goal}.") is not tried, even when it is easy: the author left it
  open.  It is marked ◆ (🔶 in the checked Markdown, the status of a
  condition left to a Proof block, with its own message, "open goal of
  the text, not tried"), its conclusion is the goal `?cN` of the Proof
  block (`Cyp File`, `Cyp Lemma`), and the nodes after it use it as any
  conclusion.  Without a Proof block (`CypFile`, the program `cyp`) the
  lemma is not defined (exit code 1), as with a step not proved.
- **Old texts.**  The texts written before the tree name a justification
  `*by X*`: it is still read as `*X*{.just}` (xtext and cyp's examples
  are written in the new format).
- **Errors** of the tree, reported at their node and line (in the checked
  Markdown and the JSON), and the node is not proved: a node with tags but
  no conclusion, two conclusions, a name out of scope or given twice in
  one scope, an unknown class, an unclosed span or div (prooftext's
  table); a fact that is no visible hypothesis or conclusion; a
  justification that names nothing known; a formula that does not parse
  ([examples/errors_demo.md](examples/errors_demo.md),
  [vernac/errors_file.md](vernac/errors_file.md)).  An error never stops
  the check: the node is not tried, and the nodes after it use its
  conclusion all the same.  A node with no conclusion (none, two, or one
  that does not parse) is used by nothing; its subnodes are checked all
  the same, and each is used by the subnodes after it.  A hypothesis or a
  variable that does not parse is left out of its node.
- **The gap tactic.**  A condition that its justifications, the rules and
  the default tactics leave open gets a last, coarse try: `cyp_gap`
  ([vernac/Gaps.v](vernac/Gaps.v)), a few bounded searches (the goal and
  the hypotheses taken apart, at most 200 steps, then a proof search of depth 4 or
  `congruence`; a case analysis on the booleans; an induction on a binder
  of the goal; a case analysis on a variable; a constructor whose arguments
  the search finds), with no time limit: a condition it cannot close costs
  a bounded search (at most 0.06 s measured).  On the conditions cyp left
  open in xtext's texts (closing steps of case analyses and inductions,
  steps that follow from earlier claims by a few applications) it closed
  99% (measured on the texts written before the tree,
  [../xtext/gaps/](../xtext/gaps/README.md)).  It is not tried on a
  node justified by a word declared as rules (*monotonicity*{.just}: those rules only).
  The header line `gaps: off` turns it off (the tutorial's
  [ch10_defaults.md](tutorial/ch10_defaults.md) is proved with it, and its
  copy [ch10_no_gaps.md](tutorial/ch10_no_gaps.md) with `gaps: off` is not;
  [examples/gaps_demo.md](examples/gaps_demo.md), written before cyp's
  other tactics improved, is now proved either way).

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

**cyp always succeeds, and leaves goals.**  cyp is not a yes/no check:
what it proves is proved, and the rest is left as goals.  `Cyp File` and
`Cyp Lemma` succeed whatever the nodes say: a condition not discharged
and the conclusion of a node with an error are goals of the Proof block,
and each error is printed with its node (❌).  They fail only when the
statement itself cannot be read (the conclusion or a hypothesis of the
statement does not parse, or it does not type-check), or on an error of
Rocq outside cyp (a library that is not found, a proof term that Rocq
rejects).  The program `cyp` always writes the checked Markdown and the
JSON, with the status of every node; its exit code is 0 when the lemma is
defined (every node proved), 1 when it is not (a node not proved or with
an error, or a statement that cannot be read: the messages say which), 2
when it cannot run (usage, `CYP_LIB` not set).

**The checked Markdown** is the text itself, with the mark of each node's
status at the start of its own text (`- ✅ ...` for an item, `[✅ ...]{.p}`
for a span) and its message in a folded block after the paragraph where it
starts.  **The JSON** (`cyp --json`) gives, for each node, its number,
its first and last lines (numbered from 0), its status, its formulas and
its message; then the declared words that its justifications use, with
the place of their declaration ("Declaring justification words", below).

## Deterministic bounds

cyp has no time limit: a time limit makes the verdict depend on the
machine and on its load.  Instead, every search that cyp runs has a fixed
bound, the same on every machine, or is a decision procedure that ends;
two have no bound at all in Rocq 9.1, and say so below: `lia` (and `nia`)
and Rocq's reduction.
The tactics that a text may name (`prooftext/tactics.elpi`), the default
tactics, the gap tactic and cyp's own search:

| tactic | what cyp runs | bound |
|---|---|---|
| `tauto` (default) | `itauto auto` | itauto's SAT solver runs on a fuel computed from the size of the formula; its leaf tactic `auto` is of depth 5 |
| `auto` | `auto` | depth 5 |
| `easy` | `easy` | a fixed set of steps |
| `firstorder` | `bounded_firstorder` ([../prooftext/Tactics.v](../prooftext/Tactics.v)) | the goal and its hypotheses taken apart, at most 200 steps (`decompose_steps`; without it, `split` on `Inductive U : nat -> Prop := cu : forall n, U (S n) -> U n` goes on for ever), then `eauto 4` (depth 4) or `congruence` |
| the gap tactic | `cyp_gap` ([vernac/Gaps.v](vernac/Gaps.v)) | `bounded_firstorder`; a case analysis on each boolean of the context, once; an induction on one binder of the goal, each tried once; a case analysis on one variable, each tried once; one constructor; each case closed by `eauto 4` or `congruence` |
| `congruence` | `congruence` | ends (a closure over the terms of the goal) |
| `ring`, `field` | `ring`, `field` | end (normal forms of polynomials) |
| `lra` (default), `nra` | Micromega: the simplex on the rationals; `nra` first adds the products of pairs of hypotheses (degree 2) | end; the size of the problem is not bounded |
| `lia` (default), `nia` (default) | `guarded_lia`, `guarded_nia` ([../prooftext/Tactics.v](../prooftext/Tactics.v)): `lia_guard`, then Micromega: the simplex, then cuts and case splits on integer variables; `nia` first adds products (degree 2) | **no bound** for the search: Rocq 9.1 has the options `Lia Depth` and `Lra Depth`, but the search does not read them (`plugins/micromega/certificate.ml`: the depth only sets `max_nb_cstr`, which nothing uses), and there is no other one.  `lia_guard` refuses, with a message, a goal with more than 50 case splits (disjunctions, `<>`, `-`, `max`, `min`, `abs`, `div`, `mod`, ... counted on the goal and the hypotheses, no search) or more than 16 hypotheses: it bounds what lia is given, not its search; the bounds are 1.5 and 2 times the largest call that succeeded in the measurement (`../xtext/gaps/README.md`, "No time limit"), and change no result of cyp's examples or of xtext's texts |
| `arith` | `first [ guarded_lia \| itauto auto ]` | those of `lia` and `tauto` |
| `reflexivity`, `assumption`, and every unification | Rocq's conversion | ends (a well-typed term has a normal form), but there is no bound on the number of reduction steps: a step that asks Rocq to compute a large value takes as long as the computation |
| cyp's search (rules) | `close`, `premises` ([vernac/elpi/check.elpi](vernac/elpi/check.elpi)) | a lemma applied to close a premise of a lemma: at most `premise-depth-max` lemmas deep (4); the goal with its head unfolded: once; a conjunction or a disjunction: split along the formula |

cyp itself never runs `interval`.

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
  and, once the word is declared with `CypJustification "name" := rules.`
  (below), the only kind tried when a node is justified by
  `*name*{.just}`: the text says why a node holds (*monotonicity*{.just}),
  the proof's files say what that means, and Rocq checks that this reason,
  and no other, closes the step ([examples/named_demo.md](examples/named_demo.md)
  with its rule file [examples/named_demo.v](examples/named_demo.v)).

A rule is an Elpi clause, so it may have a body, for example to fire only
when another rule applies.  On a node with no declared word, the rules are
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

## Declaring justification words

What a justification word means is written in the files of the proof, with
a Rocq command of [vernac/Cyp.v](vernac/Cyp.v), not hidden in cyp:

```coq
Ltac easy_check := lra.
CypJustification "checked" := easy_check.        (* *checked*{.just} runs easy_check *)

Elpi Accumulate cyp.db lp:{{
  named "monotonicity" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_r }}).
  named "monotonicity" {{ (_ * _ <= _ * _)%R }} (apply {{ Rmult_le_compat_l }}).
}}.
CypJustification "monotonicity" := rules.        (* *monotonicity*{.just}: these rules only *)
```

- `CypJustification "word" := tac.`: the word means the Ltac tactic `tac`
  (a name, possibly qualified, defined by `Ltac` before; tactic code
  `ltac:(...)` is not accepted, Rocq-Elpi cannot keep it).  Rocq resolves
  the name at the declaration: the tactic is run once on the goal `True`,
  and a name that is no Ltac tactic stops there with Rocq's error
  "Ltac1 tactic ... not found".
- `CypJustification "word" := rules.`: the word means the rules
  `named "word" ...` of `cyp.db`, which must be accumulated before (else
  an error); a node justified by it is closed by these rules only (no gap
  tactic either).
- A word is declared once: a second declaration is an error that gives
  the file and the line of the first.  A word that is also the name of a
  lemma hides it in the justifications (a warning at the declaration).  A
  name of the text in scope (a hypothesis, a node, a variable) hides a
  declared word (the order is in "The format", above).
- The binding is kept in `cyp.db` (`justification-word Word Meaning
  Origin`), visible where the file of the declaration is imported, with
  the place of the declaration: its file and line, and its library
  (`CypV.Cyp`).  A declaration in a rule file `.v` of a Markdown proof has
  its place in that file (the program `cyp` copies the file into the one it
  runs, and tells cyp where its lines come from).
- The tactics every proof text may name (`lia`, `tauto`, ...: prooftext's
  [tactics.elpi](../prooftext/tactics.elpi)) are declared at the end of
  [vernac/Cyp.v](vernac/Cyp.v) with the same command,
  `CypJustification "lia" := cyp_lia.`, so that every word has a visible
  declaration; `Cyp.v` checks that none of prooftext's is missing.  They
  are also the names a header's `by:` gives (each a declared word).
- A word that is declared nowhere, and is no name of the text or lemma,
  is an error of its node, which says how to declare it.

Where to write the declarations: in a rule file `.v` of the header
(`rules: named_demo.v`, as [examples/named_demo.v](examples/named_demo.v)),
in a library of the `require:` line, or, for `Cyp Lemma`, in the `.v` file
itself ([vernac/named_v.v](vernac/named_v.v)).

**Links.**  The JSON of a checked text (`proof.cyp.json`) lists the
declared words that its justifications use, one per line, with their
meaning and the place of their declaration:

```json
{"word":"monotonicity","meaning":"rules","library":"","file":"/…/cyp/examples/named_demo.v","line":8}
{"word":"lia","meaning":"tactic cyp_lia","library":"CypV.Cyp","file":"./Cyp.v","line":442}
```

`prooftext/pdf.sh --source-root ROOT=URL` (and `gallery.sh`, which passes
it on and copies the JSON with each text) makes each such word a link to
its declaration in the PDF and the web page: `URL` followed by the file's
path under `ROOT` and `#L` with its line (GitHub's line anchors), `ROOT`
a directory (`/…/coq_tmp`) or a logical prefix (`CypV`: `CypV.Cyp` is
`Cyp.v`):

```sh
../prooftext/pdf.sh --html --source-root "$(cd .. && pwd)=https://github.com/thery/coq_tmp/blob/main/" \
  --source-root CypV=https://github.com/thery/coq_tmp/blob/main/cyp/vernac/ examples/named_demo.checked.md
```

## The PDF

```sh
../prooftext/pdf.sh examples/square_pos.checked.md   # square_pos.checked.typ, then square_pos.checked.pdf
```

makes the PDF of a checked text with Typst, in the template that
prooftext shares with xtext
([../prooftext](../prooftext/README.md#the-pdf-of-a-proof-text-typst)):
each step has its status as a coloured mark (✔ proved, ✘ not proved, ◆
left to a Proof block, or an open goal, ▫ nothing to check: a remark),
an open goal's formula framed, cyp's message in a box under
it, and its number in the margin, the number of its condition; the
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
  several names); declared words (`CypJustification`: a tactic, rules) choose the method, the other
  names are handed to it; what a word means is declared in the proof's files;
- remarks: a text with no tag is shown and not checked;
- the method of a node may also be chosen by Elpi rules from the shape
  of its goal, written per field in a rule file;
- under a failing node, its goal and Rocq's message, in the Markdown
  output and in the editor;
- the whole checker runs inside Rocq (Rocq-Elpi), and the same proof can
  also be written as a Rocq command, `Cyp Lemma` ([vernac/](vernac/README.md)).
