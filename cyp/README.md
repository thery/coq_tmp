# cyp: coloured proofs

A proof is written in Markdown, as on paper.  cyp turns each step into a
Rocq goal, tries to prove it, and writes the proof back in Markdown, with
✅ in front of each proved step and ❌ in front of the others; under a ❌, a
folded block gives the goal and Rocq's message.  When every step is
proved, the lemma is defined in Rocq.

cyp is written in Rocq-Elpi ([vernac/](vernac/README.md)): the command
`CypFile "proof.md".` reads the Markdown, checks it and writes the
result.  The program `cyp` ([bin/cyp.ml](bin/cyp.ml)) is only a driver:
it writes the small Rocq file that loads the proof's libraries and rules
and runs this command.

It needs the opam switch `elpi4` (Rocq 9.1.1, Elpi 4.0.0, rocq-elpi with
`coq.parse.argument`, coq-elpi pull request #1133):

```sh
dune build
(cd vernac && rocq c -Q . CypV Cyp.v)                     # the cyp library
export CYP_LIB=$PWD/vernac
dune exec cyp -- examples/square_pos.md   # writes square_pos.checked.md and square_pos.cyp.json
dune exec cyp -- --conditions examples/square_pos.md   # prints the conditions, tries nothing
```

## The format

```markdown
---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia | nia
---

# square_pos

Let `a b : Z`. If `0 < a < b` then `a * a < b * b`.

- It is equivalent to prove `0 < b * b - a * a`.
- That can also be written as `0 < (b + a) * (b - a)`.
- From `0 < a < b` we have `0 < b + a` and `0 < b - a`.
```

- **The header** (between the two `---`): `require`, the Rocq preamble;
  `scope`, a scope to open; `by`, the tactics tried on a step with no
  justification; `rules`, files of rules (below), separated by spaces,
  copied in order after the preamble; `flags`, options given to
  `rocq c` (e.g. `-Q dir Name`; the directories of `-Q`, `-R`, `-I` and
  the rule files are relative to the directory of the proof, and
  `${NAME}` is the environment variable NAME, so that a proof does not
  name the directories of one machine); `lang`, the language of the text,
  `en` (default), `fr` or `it`, which gives the role words below.  There
  is no time limit per step.
- **A proposition** starts with `# name`.  Its statement is the text that
  follows, up to the first list item.
- **Formulas** are written between backticks, in Rocq syntax.  The word
  before a formula gives its role:
  - after *let*: variables (`a b : Z`);
  - after *if*, *assume*, *suppose*: hypotheses;
  - after *from*, *using*, *since*: facts used (shown, not checked);
  - after *then*, *have*, *show*, *prove*, *hence*, *so*, ...: claims;
  - in French: *soit*, *soient*, *considérons* (variables); *si*,
    *supposons*, *posons par hypothèse* (hypotheses); *à partir de*, *en
    utilisant*, *puisque*, *d'après*, *grâce à* (facts); *alors*,
    *montrons*, *nous avons*, *donc*, *ainsi*, *d'où*, *nous en déduisons*,
    *nous obtenons*, *c'est-à-dire*, ... (claims); a backward step says *il
    suffit*, *revient à* or *se réduit à*;
  - in Italian: *sia*, *siano*, *consideriamo*; *se*, *supponiamo*,
    *assumiamo*; *da*, *usando*, *poiché*, *grazie a*; *allora*,
    *mostriamo*, *dimostriamo*, *abbiamo*, *quindi*, *dunque*, *ne segue*,
    *ne deduciamo*, *otteniamo*, *cioè*; backward: *basta*, *è
    sufficiente*, *si riduce a*;
  - a formula with no such word keeps the role of the one before it;
  - a tag written right after a formula gives its role explicitly, whatever
    the words: `` `0 <= a * a`{.claim} `` (also `{.var}`, `{.hyp}`,
    `{.fact}`).  The tag is the attribute syntax of Pandoc; it does not
    appear in the output.
- **A step** is a list item.  Its claims are proved from the hypotheses
  and the claims of the steps before it, and each claim also from the
  claims before it in the same step (*we have `0 < b` and hence
  `0 < b + b`*).  A step that says *suffices*,
  *enough*, *equivalent to prove* or *written as* goes backwards: its
  claim replaces the goal, and the step checks that the new goal implies
  the old one.  It is the last phrase before the claim that counts: in
  *it is enough to check all the cases, so we have `C`*, the claim is
  announced by *so*, and the step goes forward.  At the end, the last goal must follow from all the claims.
- **A justification** is written `*by X*` in the step, as a paper says
  "by Lemma 3".  When X is made of words, it is a name: the rules of that
  name (see `named` below) if there are any, and only them; else the lemma
  X, applied, its premises closed by the rules or the default tactics;
  else the tactic X (an Ltac name, or `lia`, `lra`, `nia`, `nra`, `ring`,
  `field`, `tauto`, `auto`, `easy`, `reflexivity`, `assumption`).  X
  cannot be tactic code (`interval with (i_prec 100)`): Rocq-Elpi cannot
  yet turn a string into a tactic; name an Ltac definition instead.  A
  step with no `*by*` is closed by all the rules, then the tactics of
  `by`.
- **A local definition**: *Let `u := e`* introduces `u`, equal to `e`, for
  the steps that follow (a `let` in their goals).
- **A local scope**: a step that only introduces variables or hypotheses
  (*Let `n : nat`*, *Assume `P n`*) adds them for its sub-steps, or, if it
  has none, for the steps that follow it.  Its claims C are then known to the steps after it as `forall n, P n -> C`.
  Every claim of the scope is known after it in this generalised form.
  This is how a case of an induction is written.
- **Sub-steps** (an indented list) prove their parent's claim; the parent's
  justification then closes it from the sub-steps.

A claim that does not hold makes the following steps easier to prove, as
on paper: a red step is the one to look at first.

**Conditions.**  The text is a verification condition generator: each
step gives conditions (its claims, numbered `2`, or `2a`, `2b` for several,
`2.1` for a sub-step), which cyp discharges by its rules and default
tactics.  Inside Rocq, the conditions it does not discharge can be left to
a Proof block of ordinary tactics, `Cyp File "proof.md". Proof. ...
CypQed.` (marked 🔶 with their numbers), see [vernac/](vernac/README.md).

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
  and the only kind tried when a step says `*by name*`: the text says why
  a step holds (*by monotonicity*), the rule file says what that means,
  and Rocq checks that this reason, and no other, closes the step
  ([examples/named_demo.md](examples/named_demo.md)).

A rule is an Elpi clause, so it may have a body, for example to fire only
when another rule applies.  On a step with no `*by ...*`, the rules are
tried in order, then the default tactics.  Conjunctions and disjunctions
are split by cyp itself.  A rule file may also be a `.v` file of Rocq
text, copied into the proof as it is.  The lemmas of a field go in a
compiled library, never in a file loaded with `Load`: a lemma proved by
`interval` in a loaded file keeps its numerical check as an assumption
(`Print Assumptions` lists it as an axiom).

Example: [examples/rules_demo.md](examples/rules_demo.md) with
[examples/rules_demo.elpi](examples/rules_demo.elpi) proves its three
steps; without the rule file, `lra` proves only one.
A larger case study, a floating-point paper with a library of lemmas and
shared rules, is kept in a private branch.

## The editor

[vscode/](vscode) is a VS Code extension (plain JavaScript, nothing to
build): on saving a proof it runs `cyp --json`, colours each formula by
its role, marks each step with a green ✓ or a red ✗, and shows the goal and
Rocq's message of a failing step on hover.  Install it by linking the
directory into `~/.vscode/extensions/`; set `cyp.command` to the command
that runs cyp (for instance `opam exec --switch=elpi4 -- env
CYP_LIB=/path/to/cyp/vernac cyp`).

## Departures from the 2006 paper

cyp revives *Colouring proofs: a lightweight approach to adding formal
structure to proofs* (UITP).  It keeps its idea, a proof written as text
with formulas whose role is marked, each step checked by the prover, and
changes the rest where there is an obvious improvement:

- Markdown instead of XML tags, so that a proof reads as a normal document;
- the role of a formula is guessed from the words before it, with an
  optional tag `{.role}`, instead of a tag around every formula;
- backward steps (*it suffices to prove*) and sub-steps;
- the justification of a step is chosen by Elpi rules from the shape of
  its goal, written per field in a rule file;
- under a failing step, its goal and Rocq's message, in the Markdown
  output and in the editor;
- the text may be in English, French or Italian;
- the whole checker runs inside Rocq (Rocq-Elpi), and the same proof can
  also be written as a Rocq command, `Cyp Lemma` ([vernac/](vernac/README.md)).
