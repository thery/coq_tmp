# cyp: coloured proofs

A proof is written in Markdown, as on paper.  `cyp` turns each step into a
Rocq goal, tries to prove it, and writes the proof back as a web page where
each step is green (proved) or red (not proved, with its goal and Rocq's
message).

```sh
dune build
dune exec cyp -- examples/square_pos.md   # writes square_pos.v and square_pos.html
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
  justification; `timeout`, the seconds allowed per step (10).
- **A proposition** starts with `# name`.  Its statement is the text that
  follows, up to the first list item.
- **Formulas** are written between backticks, in Rocq syntax.  The word
  before a formula gives its role:
  - after *let*: variables (`a b : Z`);
  - after *if*, *assume*, *suppose*: hypotheses;
  - after *from*, *using*, *since*: facts used (shown, not checked);
  - after *then*, *have*, *show*, *prove*, *hence*, *so*, ...: claims;
  - a formula with no such word keeps the role of the one before it.
- **A step** is a list item.  Its claims are proved from the hypotheses
  and the claims of the steps before it.  A step that says *suffices*,
  *enough*, *equivalent to prove* or *written as* goes backwards: its
  claim replaces the goal, and the step checks that the new goal implies
  the old one.  At the end, the last goal must follow from all the claims.
- **A justification** is written `*by tactic*` in the step; otherwise the
  tactics of `by` are tried.
- **Sub-steps** (an indented list) prove their parent's claim; the parent's
  justification then closes it from the sub-steps.

A claim that does not hold makes the following steps easier to prove, as
on paper: a red step is the one to look at first.
