[Back to the README of xtext](../README.md)

# Examples and tests

The example files, the examples of the two theses, and the larger examples of Rocq's Stdlib.

## Tests

- `paper.v`: the examples of the paper: the identity, the proof (S),
  `∨intro`, commutativity of `∨` by `or_ind`, `∀m, 0 ≤ m` by `nat_ind`,
  and the three examples of the last figure (praeclarum, a symmetric and
  transitive relation is nearly reflexive, the drinker's principle).
- `lemmas.v`: `and_swap`, `or_swap`, `imp_trans`, `not_not_intro`,
  `ex_forall`, `forall_and`, `add_0_r'`, `le_add_r'`, `double_neg_em`.
- `inductive.v`: induction on `nat` with rewriting (`plus_n_Sm'`), on
  lists (`app_nil_r'`), rewriting only (`eq_trans'`), induction on a
  hypothesis `n <= m` (`le_n_S'`), a `Fixpoint` on `nat` (`le_0_n'`) and
  on lists (`length_app'`), case analysis on a boolean (`bool_cases`).

All these texts are generated in `examples/`; cyp's results are in
["Checking the texts with cyp"](checking-with-cyp.md).
## The examples of the two theses (`thesis.v`)

The proof terms are written as close as possible to the λ-terms of the
theses.

**Tauto** (Coscoy, Fig. 1.5, 2.6, 2.8, 2.11): `fun A B C h1 h2 h3 => h3 h1 h2`.
- Same: the statement (`Let A B C`, `Assume A (h1), B (h2) and A -> B -> C (h3)`).
- Different: the thesis writes one step, `En appliquant l'hypothèse h3 à
  h1 et h2 nous avons C` (its application-to-variables rule).  xtext
  writes the three hypotheses as dashed lines, then `We deduce C`, so
  that every formula is shown.  The thesis's closing `Nous avons montré
  ∀A, B, C ...` is the statement here.

**Trans_Inv** (Coscoy, Fig. 3.5-3.13 and the final form, Fig. 5.11):
`fun E R h x y z h1 h2 => h z y x h2 h1`, with `Rel`, `Trans`, `Inv` as
in the thesis.
- Same: the binders (`Let E : Set`, `Let R : Rel E`, `Assume Trans E R
  (h)`, `Let x y z : E`, `Assume Inv E R x y (h1) and Inv E R y z (h2)`),
  the two hypotheses used, then the application of `h`.
- With "that is" (mechanism (4), see ["that is"](generic-mechanisms.md#4-that-is-thesis-33-and-522-cast)) and the inferable arguments (3b),
  the text is now that of Fig. 3.13: `By h2 we have Inv E R y z, that is R
  z y`, `By h1 we have Inv E R x y, that is R y x`, `By h we have Trans E
  R, that is forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`, `We
  deduce R z x, that is Inv E R x z`, and the statement is the declared
  one, `We prove Inv E R x z`.  The step `In particular R z y -> R y x
  -> R z x` is gone: `z`, `y`, `x` are inferred (as in Fig. 5.11, `En
  appliquant h à h2 et h1`).
- Still different from Fig. 5.11: the goal `Trans E (Inv E R)` is not
  announced with its unfolding before the binders `x y z` (`Montrons
  (Trans E (Inv E R)), ce qui est équivalent à ∀x, y, z ...`): the
  statement is `Let x y z : E`, `Assume ...`, as the λ-term gives it.
  With the staged translation, the statement is `We prove Trans E (Inv E
  R)`, the binders are a step, and its conclusion says the unfolding
  (`that is Trans E (Inv E R)`): see ["The staged translation"](staged-translation.md).

**ABCD** (Coscoy, Fig. 4.28, 5.5, 5.6):
`fun A B C D h1 h2 h3 h4 => h1 h4 (h2 h4 (h3 h4)) (h3 h4)`.
- Same: the same three intermediate results, in the same order
  (`C`, then `B` from `h2`, then `C` again, then `D`).
- Different: the thesis names them (`P1`, `P2`, `P3`) and writes one line
  each (`En appliquant h3 à h4, nous avons C (P1)`); xtext nests them as
  dashed subproofs with the hypotheses shown.  The thesis's Fig. 5.6 has a
  typo (`D (h4)` for `A (h4)`).

**or_com** (Coscoy, Fig. 6.2, 6.3, 6.5):
`fun A B H => or_ind (fun H0 => or_intror H0) (fun H0 => or_introl H0) H`.
- Same as Fig. 6.5 (ElimOpen / ElimCase / ElimClose): `We prove B \/ A by
  case analysis on A \/ B (H)`, two cases with `Assume A (H0)` and `By
  definition of or ..., from A (H0) we deduce B \/ A`, then `We have B \/ A
  in all cases`.
- Different: the names of the rules are given, and each case states its
  goal (`Case 1: we prove A -> B \/ A`).

**or_sym_nd** (Théry, Fig. 3.3): `a \/ b -> b \/ a` with a `match`.
The thesis's text: `Supposons a ∨ b (1) / a ∨ b par (1) / Il y a donc deux
cas / Si a (2) / a par (2) / donc b ∨ a évidemment / Si b (3) ... / nous
avons b ∨ a dans les deux cas / nous avons prouvé a ∨ b ⊃ b ∨ a`.  xtext
gives the same steps in the same order, except the first `a ∨ b par (1)`,
which is in the case-analysis line (`on a \/ b (H1)`), and the
hypothesis of the implication, which is in the statement.

**praeclarum_nd** (Théry, section 3.3.3):
`conj (proj1 H1 (proj1 H2)) (proj2 H1 (proj2 H2))`.  The thesis's final
text: `x par (2) / Nous en déduisons z par (1) / y par (2) / Nous en
déduisons t par (1) / Ceci réuni donne z ∧ t`.  Same structure (two
modus ponens, then the conjunction), but `proj1` and `proj2` are Rocq
theorems, not rules, so each ∧-elimination costs xtext two lines (`Using
proj1 we get ...`, `In particular ...`) where the thesis writes `par (1)`.

**ADD0** (Théry, section 4.9.2, HOL): `nat_ind (fun m => m + 0 = m)
eq_refl (fun m IH => f_equal S IH) m`.  An induction with a base case and
an inductive case, as in the thesis's HOL session.  Coscoy's rules
(6.3.3, 6.3.4) give the generalised statement, `(base)` and
`(inductive)`, and `Assume by induction hypothesis m0 + 0 = m0 (IH)`.

### xtext's wordings and Théry's Figures 3.4-3.6

| rule | Théry 1994 | xtext |
|---|---|---|
| ∧ intro | `ceci réuni donne A ∧ B` | `So by definition of and (conj), we have A /\ B` |
| ∨ intro | `donc, A ∨ B évidemment` | `By definition of or (or_introl), ... we have A \/ B` |
| ⊃ intro | `Supposons A (i)` ... `nous avons prouvé A ⊃ B` | `Assume A (i)` ... `We have proved A -> B` |
| ¬ intro | `Supposons A (j)` ... `d'où ¬A (en niant j)` | as ⊃ intro: `Assume A (j)` ... `We have proved A -> False` |
| ∀ intro | `Considérons un c arbitraire` ... `comme c était arbitraire, nous avons ∀x A` | `Let us consider an arbitrary c : T` ... `We have τ, since c is arbitrary` |
| ∃ intro | `par conséquent ∃x A` | `By definition of ex (ex_intro) with witness c, we have ...` |
| ∧ elim | `A ∧ B, donc C` | one case: `Going back to the definition of and ... in A /\ B (h)`; with `proj1`: `Using proj1`, `In particular` |
| ∨ elim | `Il y a donc deux cas: si A (k) ... si B (l) ... nous avons C dans les deux cas` | `We prove C by case analysis on A \/ B (h) ...: Case 1 ... Case 2 ... We have C in all cases` |
| ⊃ elim | `nous en déduisons B` | `We deduce B` |
| ¬ elim | `il y a une contradiction` | `We deduce False` |
| ∀ elim | `en particulier A[x\e]` | `In particular A[x\e]` |
| ∃ elim | `Dans ceci, choisissons c, tel que A[x\c] (m)` ... `(indépendamment de c)` | `Going back to the definition of ex ... Let us consider an arbitrary c ... Assume A (m)` |
| ⊥ elim | `(donc C)` | `By contradiction (False, ...), from False (f) we can deduce C` |
| closure | `A par (n)` | `By n we have A` |

The structure is the same as xtext's (the paper of 1995 descends from it):
a hypothesis opens an indented block, a rule with several premises lists
them, then states its conclusion.  The differences: xtext names the
constructors and theorems, has no special words for `¬` (a negation is
an implication to `False` in Rocq), and states the goal of each case.

The text of an **incomplete proof** (section 3.3.3), where each open goal
is written `Prouvez G` at its place, is now `Explain_partial` (see ["Proofs in progress"](contraction-eliminations-partial.md#8-proofs-in-progress-l-thérys-thesis-333)).

## More examples: theses, Stdlib

Files: `thesis.v` (the theses' examples, above), `stdlib.v` (40 lemmas
of Rocq's Stdlib, explained from the library itself: `Time Explain
app_assoc to ...`).  `measure.sh f.v` prints, for each text, the time of
`Explain` (Rocq's `Time`), the number of list items and the size;

What breaks or becomes unreadable on the large ones:

- **Generated proofs are explained as they are.**  `Nat.add_comm`,
  `Nat.mul_comm`, ... are proved with setoid rewriting: their texts (200-480
  items) are mostly about `Morphisms.Proper`, `ProperProxy`,
  `RelationClasses.Reflexive`, the internals of `rewrite`, not about
  arithmetic.  The certificates of `lia`, `ring` or `interval` appear as
  local definitions (`Let __ff be Tauto.IMPL (...)`) and lines of
  1500-2200 characters.  Now partly handled, see ["Tactic-built
  subproofs"](generic-mechanisms.md#5-tactic-built-subproofs-thesis-54-the-pragmatic-method).
- **Implicit arguments.**  Rocq prints `Equivalence eq` or `length [] =
  0` without the type, and these formulas do not type-check again: cyp
  marks them as errors, and all the steps after them too.  This is most of
  the "not proved" of the `Nat.*` and `length_*` texts.  Now handled,
  see ["Formulas that type-check again"](generic-mechanisms.md#3a-formulas-that-type-check-again-thesis-54-applied-to-formulas).
- **Local definitions** (`Let hyp_list be nil`) had no form in cyp, so a
  later formula that used `hyp_list` was a Rocq error.  They are now
  written as cyp's local definitions (see ["Local definitions"](generic-mechanisms.md#local-definitions)).
- **Size**: `Nat.le_trans` (484 items) is generated in 0.5 s, but cyp
  does not finish it within its limit (300 s).
