# cyp inside Rocq: Cyp File and Cyp Lemma

The library [Cyp.v](Cyp.v) (Rocq-Elpi, opam switch `elpi4`) is cyp
itself: what a proof means, how its steps are checked, and how the
Markdown is read and written back.  It gives two commands.

Build: `rocq c -Q . CypV Cyp.v`.

## Cyp File: a proof in Markdown

```coq
From Stdlib Require Import ZArith Lia.
From CypV Require Import Cyp.
Open Scope Z_scope.
CypFile "square_pos.md".
```

reads the proof, parses each formula between backticks in the context of
its step (`coq.parse.argument`, in the scope of the header's `scope:`),
checks every step, writes `square_pos.checked.md` and `square_pos.cyp.json`
next to it, and defines the lemma when every step is proved.  The program
`cyp` ([../bin/cyp.ml](../bin/cyp.ml)) writes this small file from the
proof's header (its `require:`, `rules:` and `flags:`) and runs it; the
Markdown format is described in [../README.md](../README.md).

Tests here: [since_demo.md](since_demo.md) (a claim used by the next claim
of the same step), [scope_demo.md](scope_demo.md) (nested local scopes),
[type_demo.md](type_demo.md) (variables of type `Type`, in the statement
and in a scope), [square_pos_fr.md](square_pos_fr.md) and [square_pos_it.md](square_pos_it.md)
(French and Italian).

## The text as a verification condition generator

Each step gives conditions, goals in their own context, numbered after the
step in Dewey notation: `2.1` is the first sub-step of step 2, `2a` and
`2b` the two claims of step 2, `0` the statement after the steps.  In a
goal, the claims of the earlier steps are plain hypotheses (`c1a`,
`c2_1`), whatever their proof.  cyp discharges each condition by its rules
and default tactics; with a Proof block, the conditions it does not
discharge are the goals of the block, in the order of the text, each
labelled with its number (`condition := cyp_condition "1b"`):

```coq
Cyp File "vc_file.md".
Proof.
  - apply Z.sqrt_nonneg.      (* condition 1a *)
  - apply Z.sqrt_nonneg.      (* condition 1b *)
CypQed.
```

The goal of condition 1b reads

```
  a, b : Z
  H : 0 <= a
  Hb : 0 <= b
  c1a : 0 <= Z.sqrt a
  condition := cyp_condition "1b" : unit
  ============================
  0 <= Z.sqrt b
```

and the checked Markdown marks the step 🔶 **[1a, 1b]**
([vc_file.md](vc_file.md), [vc_file.v](vc_file.v); the same with Cyp
Lemma: [vc_demo.v](vc_demo.v)).  The proof is closed by `CypQed.`, not
`Qed.` (Rocq-Elpi does not let `Qed` close a proof opened by an Elpi
command).  The goals cannot yet be selected by their number (`[c1b]:
tac`): Rocq-Elpi does not keep the name of a hole it creates.  The label
`condition` is removed from the proof term before the lemma is defined.

`CypFile "proof.md".`, used by the program `cyp`, has no Proof block:
a condition it does not discharge is ❌ and the lemma is not defined.

**Bare mode.**  With `#[bare]` (`#[bare] Cyp File "p.md".`, `#[bare] Cyp
Lemma ...`), nothing is tried: every condition is a goal of the Proof
block ([bare_demo.v](bare_demo.v)).  `#[bare] CypFile "p.md".` only
prints the conditions with their contexts; the program `cyp` does it with
`cyp --conditions p.md`.

**The gap tactic.**  A condition that the rules and the default tactics
leave open is tried with `cyp_gap` ([Gaps.v](Gaps.v)) before it is left
to the Proof block; `#[gaps="off"]` (`#[gaps="off"] Cyp Lemma ...`, or
the header line `gaps: off` of a Markdown proof) turns it off.

**Timing.**  With the environment variable `CYP_TIME` set, cyp prints the
time spent on each condition (`cyp: time 2a 1234 ms`).

**Justifications.**  A justification that is neither a rule name, a lemma
name nor a tactic name (for instance tactic code) is not run: its
condition is left open.

## Cyp Lemma: the same proof as a Rocq command

The statement is an ordinary lemma statement, the body a list of steps
mixing words (strings) and formulas (Rocq terms, parsed by Rocq):

```coq
From Stdlib Require Import ZArith Lia PrimString List.
From CypV Require Import Cyp.
Import ListNotations.
Open Scope Z_scope.
Open Scope pstring_scope.

Cyp Lemma square_pos (a b : Z) (H : 0 < a < b) : a * a < b * b :=
  [ "It is equivalent to prove" (0 < b * b - a * a) ;
    "That can also be written as" (0 < (b + a) * (b - a)) ;
    "From" (0 < a < b) "we have" (0 < b + a) "and" (0 < b - a) ].
Proof. CypQed.
```

defines `square_pos`
([square_pos.v](square_pos.v)); a word `"by X"` in a step is its
justification ([named_v.v](named_v.v)).  A false step leaves a condition
that the Proof block cannot prove ([wrong.v](wrong.v)).
(A lemma of the private case study has also been written this way.)

## How it works

The Elpi files of [elpi/](elpi):

- `text.elpi` (with prooftext's `formulas.elpi` and `tactics.elpi`: the
  classes of the roles, the syntax `*by X*`, the tactics a text may name):
  words, formulas, tags `{.role}`, names `(h)`, the
  justification `*by X*`, and the role of a formula from the last phrase
  before it;
- `vocab_en.elpi`, `vocab_fr.elpi`, `vocab_it.elpi`: the phrases of each
  language and the role they give;
- `check.elpi`: closing a goal by the step's justification, the rules of
  the database `cyp.db`, or the default tactics;
- `gaps.elpi`: the gap tactic, a last try on a condition left open
  (`cyp_gap` of [Gaps.v](Gaps.v), a bounded search), and its switch;
- `command.elpi`: what the commands share (reading a file, counting,
  defining the lemma);
- `proof.elpi`: the conditions of the steps and the proof of the statement;
  a forward claim is `cyp_have C G P (fun c : C => ...)`, a backward step a proof of `C -> Goal` applied
  to a proof of `C`, a local scope a proof of its claims generalised over
  its variables and hypotheses; the proof of several claims (of a scope,
  or of a step with sub-steps) is given once to `cyp_have` and each claim
  is a projection of it, so that the proof term grows linearly with the
  nesting of the steps ([nest_demo.md](nest_demo.md): 12 nested steps of
  two claims, type-check and definition 31.7 s and 12.1 s before, 37 ms
  and 35 ms after);
- `markdown.elpi`: reading the Markdown, writing the checked Markdown and
  the JSON for the editor.

The default tactics (`lia`, `lra`, ...) are called through a table of Ltac
definitions in [Cyp.v](Cyp.v): Rocq-Elpi cannot yet run a tactic given by
its name or its code as a string.

The proof term is built by cyp and type-checked by Rocq before the lemma is
defined: `Print Assumptions` shows only the axioms of the libraries used.
