[Back to the README of xtext](../README.md)

# Contraction, eliminations by their type, proofs in progress

The contraction of application steps, the elimination principles recognised by their type, and the texts of proofs in progress.

## (2) Contraction of application steps (thesis 3.4.2, Fig. 3.11-3.13)

A modus ponens step lists its premises as dashed subproofs.  A premise
that is itself an application step (`We deduce B`, `In particular ...`),
used only there, can be **contracted**: its own premises take its place,
and its conclusion disappears.  This is the thesis's "contraction de
l'application" (Fig. 3.11), applied to the text.  Three strategies:

- `none`: no contraction (the texts of the previous rounds);
- `maximal`: every such premise is contracted (the thesis's maximal
  contraction, Fig. 3.12);
- `guarded` (default): a premise is contracted only if (1) the step still
  follows from its new premises, checked by one of the tactics of
  `xtext-guard-tactic` (cyp's default ones: `tauto`, `congruence`, `lia`,
  `firstorder`, `auto`, 1 s each).  The tactic that closes the last
  accepted configuration becomes the step's justification (`By
  *auto*{.just} we deduce C`), so that cyp runs the same tactic.  (2) Its line has no "that
  is", so
  no conversion step is hidden (the thesis's guarded contraction keeps the
  type expressions that belong to a conversion, Fig. 3.13).

Parameters: the switch `contraction` (see ["Switches"](../README.md#switches)) and, in `xtext.db`,
`xtext-guard-tactic Ltac Text`.  The decision is greedy, premise by premise,
in the order of the text.

Limits:
- Only application steps are contracted, not the rules for
  constructors, eliminations or rewriting.
- The guard is checked with the premises of the step only, not with all
  the claims before it as cyp does.  It is conservative.
- Contraction can repeat a line: `ABCD` reads `By h4 we have A` four
  times.
- On propositional proofs `tauto` always succeeds, so guarded is maximal
  there; the two differ on arithmetic and rewriting (`Nat.*`).

Example, `ABCD` (Fig. 5.6 of the thesis has the three intermediate
results `P1`, `P2`, `P3`): with contraction, the text is the eight uses
of hypotheses (12 items become 9) and `We deduce D`.  The thesis keeps the
three named intermediate results, which xtext's contraction drops.

## (6) Elimination principles recognised by their type (thesis 6.4.2)

A constant is an elimination principle if its type has this shape, with
no condition on its name:
- parameters;
- a motive `P`, whose type ends in `Prop`;
- between them and the object, binders that are branches (their
  conclusion is `P` applied) or indices (not propositions);
- the eliminated object, of an inductive type `I`;
- a conclusion that is `P` applied to the object (kind 2) or `P` (kind 1:
  the object is a proof).

The type of the object must not mention `P`.  Without this condition,
`proj1 : forall A B, A /\ B -> A` would be read as an elimination with
motive `A`.  Induction hypotheses are still the branch binders whose type
mentions `P`.

Tests (`elim_type.v`):
- `half_le` is proved by `induction n using strong_induction`, a
  course-of-values principle defined in the file: `By definition of nat
  (strong_induction), ...`, with `Assume by induction hypothesis forall
  m, m < n0 -> m / 2 <= m (IH)`.
- `even_or_odd` uses `two_step` (`P 0 -> P 1 -> (forall n, P n -> P (S
  (S n))) -> forall n, P n`, as `list_2_ind` in 6.4.2): `by induction
  (nat, two_step)`, Case 1 (base), Case 2 (base), Case 3 (inductive).

No regression: with `none`, the 76 earlier texts are the same, byte for
byte, as before this round.

## (8) Proofs in progress (L. Théry's thesis, 3.3.3)

`ExtractText_partial.` (or `ExtractText_partial to "f.md".`), inside a proof,
prints the text of the proof so far.  Each open goal is written `Prove
G` at its place, as the thesis's `Prouvez G`.  The open goals are the holes
of the partial proof term; their statements are their types.

Limit: rocq-elpi gives the partial proof term only to a command that
closes the proof, so `ExtractText_partial` ends the proof, as `Abort` does.
In an editor, undo it to go on.

Tests (`partial.v`, texts `examples/*_partial*.md`):
- `or_swap_partial`, after `destruct`: two cases, each `Prove B \/ A`;
- `add_0_r_partial`, after `induction` and the base case: the inductive
  case is `Prove S m + 0 = S m`;
- `praeclarum_partial1` and `2`, the session of section 3.3.3: after
  `split`, `Prove z` and `Prove t`, then `So by definition of and (conj)`,
  as the thesis's `Prouvez z / Prouvez t / Ceci réuni donne z ∧ t`.  After
  the first conjunct, `We deduce z` (from `Hx` and `Hxz`) and `Prove t`.

## Measurements

All 78 texts (the 76 earlier ones and the two of `elim_type.v`), with each
contraction strategy.  The generation time is the sum of Rocq's `Time`
over the texts; the guard costs it.

| strategy | list items | characters | generation time (s) |
|---|---|---|---|
| none | 1919 | 288045 | 13.6 |
| maximal | 1720 | 267311 | 13.6 |
| guarded | 1818 | 279926 | 33.5 |

Texts that change with the strategy:

| example | items none / maximal / guarded | chars none → guarded |
|---|---|---|
| S_proof | 6 / 5 / 5 | 484 → 466 |
| nearly_reflexive | 9 / 8 / 8 | 960 → 936 |
| imp_trans | 5 / 4 / 4 | 444 → 426 |
| length_app_fix | 14 / 13 / 13 | 1552 → 1495 |
| ABCD | 12 / 9 / 9 | 720 → 638 |
| praeclarum_nd | 13 / 11 / 11 | 1082 → 1042 |
| std_app_assoc | 36 / 35 / 35 | 3469 → 3382 |
| std_app_nil_r | 28 / 27 / 27 | 2633 → 2552 |
| std_length_app | 15 / 14 / 14 | 1908 → 1849 |
| std_in_map | 36 / 34 / 34 | 3149 → 3045 |
| std_Nat_add_comm | 85 / 66 / 75 | 11659 → 10948 |
| std_Nat_add_assoc | 105 / 82 / 93 | 15181 → 14188 |
| std_Nat_mul_comm | 85 / 66 / 75 | 11657 → 10946 |
| std_Nat_le_trans | 112 / 73 / 110 | 21247 → 21059 |
| std_Nat_add_0_r | 104 / 82 / 91 | 14066 → 13115 |
| std_Nat_add_succ_r | 87 / 68 / 75 | 12046 → 11167 |
| std_Nat_le_refl | 16 / 15 / 15 | 1784 → 1730 |
| std_Nat_lt_irrefl | 35 / 28 / 32 | 4457 → 4298 |
| std_Nat_mul_1_r | 89 / 70 / 80 | 12345 → 11719 |
| half_le | 36 / 29 / 30 | 6438 → 5345 |
| even_or_odd | 27 / 27 / 27 | 3410 → 3410 |


- `maximal` contracts more steps of the `Nat.*` texts than `guarded`;
  a contracted step that cyp's tactics cannot close becomes one more red
  step, which is why `guarded` is the default.

The texts in progress (`*_partial*.md`) have one `Prove G` step per open
goal.  They are not counted above.
