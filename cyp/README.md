# cyp: coloured proofs

A proof is written in Markdown, as on paper.  `cyp` turns each step into a
Rocq goal, tries to prove it, and writes the proof back in Markdown, with
✅ in front of each proved step and ❌ in front of the others; under a ❌, a
folded block gives the goal and Rocq's message.

```sh
dune build
dune exec cyp -- examples/square_pos.md   # writes square_pos.cyp.v and square_pos.checked.md
```

`rocq c` must be in `PATH` (or set `CYP_ROCQ`), with the libraries the
proof needs.

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
  the rule files are relative to the directory of the proof); `lang`, the language of the text, `en`
  (default), `fr` or `it`, which gives the role words below; `timeout`, the seconds
  allowed per step (10).
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
  and the claims of the steps before it.  A step that says *suffices*,
  *enough*, *equivalent to prove* or *written as* goes backwards: its
  claim replaces the goal, and the step checks that the new goal implies
  the old one.  It is the last phrase before the claim that counts: in
  *it is enough to check all the cases, so we have `C`*, the claim is
  announced by *so*, and the step goes forward.  At the end, the last goal must follow from all the claims.
- **A justification** is written `*by tactic*` in the step; otherwise the
  tactics of `by` are tried.
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

## Rules: choosing the justification with Elpi

A field has its own way of proving things: products of nonnegative reals
are compared by a monotonicity lemma, rounding errors by a lemma of Flocq,
bounds by `interval`.  This knowledge goes in rule files named in the
header (`rules: float.elpi my_proof.elpi`), not in cyp.

The proved facts the rules use are ordinary Rocq lemmas, in a library the
proof loads in its `require:` field.  The rules themselves are Elpi
clauses, in files `.elpi`, added to the database `cyp.db` (defined in
[rules/cyp_rules.v](rules/cyp_rules.v)):

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

On a step with no `*by ...*`, the rules are tried in order, then the
default tactics.  Conjunctions and disjunctions are split by cyp itself.
A rule file may also be a `.v` file of Rocq text, copied into the proof
as it is.  Rule files are copied, never loaded with `Load`: a lemma
proved by `interval` in a loaded file keeps its numerical check as an
assumption (`Print Assumptions` lists it as an axiom).

Example: [examples/rules_demo.md](examples/rules_demo.md) with
[examples/rules_demo.elpi](examples/rules_demo.elpi) proves its three
steps; without the rule file, `lra` proves only one.
A larger example: [exp/](exp/README.md), proofs of lemmas of the CORE-MATH
exp paper with a library of float lemmas (`exp/float_lemmas.v`) and
shared rules (`exp/float.elpi`).

**The cache.**  cyp keeps, next to the proof, a file `*.cyp-cache` of the
steps it proved; a step whose preamble, goal and tactic have not changed
since is not checked again.  While a proof is being written, only the
changed steps and those not yet proved are run.

## The editor

[vscode/](vscode) is a VS Code extension (plain JavaScript, nothing to
build): on saving a proof it runs `cyp --json`, colours each formula by
its role, marks each step with a green ✓ or a red ✗, and shows the goal and
Rocq's message of a failing step on hover.  Install it by linking the
directory into `~/.vscode/extensions/`; set `cyp.command` to the command
that runs cyp.

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
  output and in the editor.
