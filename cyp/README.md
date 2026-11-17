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
  justification; `rules`, a file of rules (below); `flags`, options given to
  `rocq c` (e.g. `-Q dir Name`); `timeout`, the seconds
  allowed per step (10).
- **A proposition** starts with `# name`.  Its statement is the text that
  follows, up to the first list item.
- **Formulas** are written between backticks, in Rocq syntax.  The word
  before a formula gives its role:
  - after *let*: variables (`a b : Z`);
  - after *if*, *assume*, *suppose*: hypotheses;
  - after *from*, *using*, *since*: facts used (shown, not checked);
  - after *then*, *have*, *show*, *prove*, *hence*, *so*, ...: claims;
  - a formula with no such word keeps the role of the one before it;
  - a tag written right after a formula gives its role explicitly, whatever
    the words: `` `0 <= a * a`{.claim} `` (also `{.var}`, `{.hyp}`,
    `{.fact}`).  The tag is the attribute syntax of Pandoc; it does not
    appear in the output.
- **A step** is a list item.  Its claims are proved from the hypotheses
  and the claims of the steps before it.  A step that says *suffices*,
  *enough*, *equivalent to prove* or *written as* goes backwards: its
  claim replaces the goal, and the step checks that the new goal implies
  the old one.  At the end, the last goal must follow from all the claims.
- **A justification** is written `*by tactic*` in the step; otherwise the
  tactics of `by` are tried.
- **A local scope**: a step that only introduces variables or hypotheses
  (*Let `n : nat`*, *Assume `P n`*) adds them for its sub-steps, or, if it
  has none, for the steps that follow it.  Its result, `forall n, P n -> C`
  with C the last claim of the scope, is then known to the steps after it.
  This is how a case of an induction is written.
- **Sub-steps** (an indented list) prove their parent's claim; the parent's
  justification then closes it from the sub-steps.

A claim that does not hold makes the following steps easier to prove, as
on paper: a red step is the one to look at first.

## Rules: choosing the justification with Elpi

A field has its own way of proving things: products of nonnegative reals
are compared by a monotonicity lemma, rounding errors by a lemma of Flocq,
bounds by `interval`.  This knowledge goes in a rule file, named in the
header (`rules: my_rules.v`), not in cyp.

A rule file is Rocq text, put after the preamble.  Its rules are Elpi
clauses added to the database `cyp.db` (defined in
[rules/cyp_rules.v](rules/cyp_rules.v)):

```coq
Ltac real_lra := lra.
Elpi Accumulate cyp.db lp:{{
  justify {{ (_ * _ <= _ * _)%R }} (lemma {{ Rmult_le_compat _ _ _ _ _ _ _ _ }}).
  justify {{ (_ <= _)%R }} (ltac "real_lra").
}}.
```

- `justify Pattern (ltac "name")`: on a goal that matches `Pattern`, try
  the Ltac tactic `name`, which must close it.
- `justify Pattern (lemma T)`: apply `T`, then close each premise with
  the rules again.

On a step with no `*by ...*`, the rules are tried in order, then the
tactics of `by`.  Example: [examples/rules_demo.md](examples/rules_demo.md)
with [examples/rules_demo_rules.v](examples/rules_demo_rules.v) proves its
three steps; without the rule file, `lra` proves only one.

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
