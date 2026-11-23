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
  `firstorder`, `auto`, with no time limit and the bounds below).  The tactic that closes the last
  accepted configuration becomes the step's justification (`By
  *auto*{.just} we deduce C`), so that cyp runs the same tactic.  (2) Its line has no "that
  is", so
  no conversion step is hidden (the thesis's guarded contraction keeps the
  type expressions that belong to a conversion, Fig. 3.13).

**What is the thesis's and what is xtext's.**  The thesis's guarded
contraction (3.4.2, Fig. 3.11 and 3.13) is syntactic: it contracts only
where no type expression of a conversion is lost (condition (2)); it runs
no tactic.  It is what the staged translation (the default) does
(`staged.elpi`, see ["The staged translation"](staged-translation.md)).
Condition (1), "the contracted step still follows by one of the
tactics", is not the thesis's: it is xtext's addition, in the direct
translation's contraction (`applications.elpi`), made so that cyp can
check the text: the tactic that closed the step is named in it, and cyp
runs that tactic the same way.

**No time limit.**  The guard's tactics, and the tactics tried on long
subproofs (`xtext-tactic`, see ["Tactic-built subproofs"](generic-mechanisms.md#5-tactic-built-subproofs-thesis-54-the-pragmatic-method)), run with no time limit, so that the
text does not depend on the speed of the machine.  Each is the tactic
that cyp runs for its name ([cyp's README, "Deterministic
bounds"](../../cyp/README.md#deterministic-bounds)), with the same bound:

| name in the text | what xtext runs (`ExtractText.v`) | bound |
|---|---|---|
| `tauto` | `itauto auto` (coq-itauto, with `Itauto Classic`) | itauto's SAT solver runs on a fuel computed from the size of the formula; its leaf tactic `auto` is of depth 5 |
| `auto` | `auto` | depth 5 |
| `firstorder` | `bounded_firstorder` ([../../prooftext/Tactics.v](../../prooftext/Tactics.v)) | at most 200 steps taking the goal and its hypotheses apart, then `eauto 4` or `congruence` |
| `congruence` | `congruence` | ends (a closure over the terms of the goal) |
| `lia` | `guarded_lia`: `lia_guard`, then `lia` ([../../prooftext/Tactics.v](../../prooftext/Tactics.v)) | `lia` has **no bound** in Rocq 9.1 (the options `Lia Depth` and `Lra Depth` are not read by the search, as cyp's README says); `lia_guard` refuses a goal with more than 50 case splits or 16 hypotheses (a count on the goal's shape, no search), measured on every call of the texts (`../gaps/README.md`, "No time limit"); it bounds what `lia` is given, not its search |
| `arith` | `first [ guarded_lia \| itauto auto ]` (cyp's `cyp_arith`) | those of `lia` and `tauto` |

**The word `arith`.**  A step closed by the guard, or a long subproof
closed by a tactic of `xtext-tactic`, whose conclusion is arithmetic is
first tried with `arith` (`xtext-arith-tactic`), and then reads `By
*arith*{.just} ...`.  The rule is on the conclusion's shape only
(`arith-conclusion`, `elpi/transducer.elpi`): under its `forall`s and
implications (the step's premises), an equality on `nat`, `Z`, `N` or `R`,
an order `<=`, `<`, `>=`, `>` on them, or the negation of one of these
(`<>`).  `arith` runs `lia`, then `tauto` (`itauto auto`), the same
tactic as cyp's word `arith`; both lists already have `lia` and `tauto`,
so the same steps are closed and only their name changes.  A step whose
conclusion is arithmetic but that only `congruence`, `firstorder` or
`auto` closes keeps that name, and an equivalence (`<->`) is not
arithmetic.

Parameters: the switch `contraction` (see ["Switches"](../README.md#switches)) and, in `xtext.db`,
`xtext-guard-tactic Ltac Text`.  The decision is greedy, premise by premise,
in the order of the text.

Limits:
- Only application steps are contracted, not the rules for
  constructors, eliminations or rewriting.
- The guard is checked with the premises of the step only, not with all
  the claims before it as cyp does.  It is conservative.
- Contraction can repeat a line: `ABCD` in the direct translation
  (`examples-direct/ABCD.md`) reads `By h4 we have A` four
  times.
- On propositional proofs `tauto` always succeeds, so guarded is maximal
  there; the two differ on arithmetic and rewriting (`Nat.*`).

Example, `ABCD` in the direct translation (`examples-direct/ABCD.md`;
Fig. 5.6 of the thesis has the three intermediate
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
prints the text of the proof so far, as `ExtractText` does (plain text,
the tagged format with `#[tags]` or in a file).  Each open goal is written `Prove
G` at its place, as the thesis's `Prouvez G`, in the tagged format
``Prove `G`{.goal}.``: the role of an open goal (prooftext's format,
"Open goals"), which cyp does not try and leaves as a goal of the Proof
block, and which the PDF and the web page frame.  The plain text keeps
`Prove G.`.  The open goals are the holes
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
  the first conjunct, `Applying Hxz to Hx, we have z` and `Prove t`.

## Measurements

The texts of the seven example files of `make_variant.sh` (`paper`,
`lemmas`, `inductive`, `thesis`, `stdlib`, `elim_type`, `partial`; 73
texts, the texts in progress left out of the counts), rerun 2026-11-23
with each contraction strategy in both translations, before and after
the time limits were removed (the guard's tactics had 1 s each, the
tactics of long subproofs 2 s).  The generation time is the sum of
Rocq's `Time` over the files, on one machine (it is a measurement, not a
bound: the texts no longer depend on it).

| translation | strategy | list items | characters | time with limits (s) | time without (s) |
|---|---|---|---|---|---|
| staged | none | 1414 | 205233 | 7.7 | 8.3 |
| staged | maximal | 872 | 106023 | 6.1 | 6.6 |
| staged | guarded | 905 | 113547 | 6.3 | 6.9 |
| direct | none | 1258 | 173166 | 7.7 | 8.1 |
| direct | maximal | 1069 | 154870 | 7.7 | 8.0 |
| direct | guarded | 1167 | 166532 | 8.7 | 9.2 |

(items and characters: without time limits.)  In the staged
translation the guarded contraction is the thesis's, syntactic, and
costs nothing; in the direct translation the guard's tactics cost about
1 s.  An earlier round (before the staged translation and the tree, 78
texts) had measured 13.6 s for none and maximal and 33.5 s for guarded,
in the direct translation.

Removing the time limits changed no contraction (every strategy contracts
the same premises), and changed the texts in two ways, both because
`tauto` is now run as cyp runs it, `itauto auto`, whose leaf tactic
`auto` uses the hints of the standard library (`plus_n_O`, `plus_n_Sm`,
...), where `tauto` only reasoned on the connectives:

- a contracted step that `congruence`, `firstorder` or `lia` closed is
  now closed by `tauto`, the first tactic of `xtext-guard-tactic`, and
  says so (`By *tauto*{.just} we deduce ...`): 23 steps of 10 texts of
  `examples-direct/`;
- a long subproof that `lia` closed is now closed by `tauto`, the first
  of `xtext-tactic` (`std_Nat_add_0_r`, `std_Nat_add_succ_r`, and a step
  of `examples-direct/std_Nat_add_succ_r.md`), and the proof of
  `std_andb_assoc`, a case analysis on its three booleans before, that
  neither `tauto` nor `lia` closed, is now one step, `By *tauto*{.just} we
  have ...`.

Then the word `arith` (same day): every step above whose conclusion is
arithmetic reads `By *arith*{.just}`, with no other change (the table
above is of the texts before it).  In `examples/`: `std_Nat_add_0_r` and
`std_Nat_add_succ_r` (tauto), `std_Nat_add_assoc`, `std_Nat_add_comm`,
`std_Nat_mul_comm` (lia); `std_andb_assoc` (an equality on `bool`) stays
`tauto`, and the three `lia` steps whose conclusion is a disjunction
(`even_or_odd`, `std_Nat_le_trans`) stay `lia`.  In `examples-direct/`, 10
steps of 10 texts: 5 from `tauto` (`length_app_fix`, `std_length_app`,
`std_Nat_add_0_r`, `std_Nat_add_succ_r`, `std_Nat_mul_1_r`) and 5 from
`lia` (`half_le`, `std_Nat_add_assoc`, `std_Nat_add_comm`,
`std_Nat_lt_irrefl`, `std_Nat_mul_comm`).

Texts that change with the strategy (the earlier round, direct
translation, not rerun):

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
goal.  They are not counted above.  Checked by cyp, each open goal is ◆
(not tried, left to a Proof block), and the lemma is not defined.
