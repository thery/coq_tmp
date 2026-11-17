# xtext: proofs as text

`Explain foo.` prints the proof of the constant `foo` as text.  It follows
the *basic transducer* of *Extracting Text from Proofs* (Y. Coscoy,
G. Kahn, L. Théry, TLCA 1995, section 3.1), extended to inductive types
after chapter 6 of Y. Coscoy's thesis *Explication textuelle de preuves
pour le calcul des constructions inductives* (Nice, 2000).  The text is
coarse but faithful: one list item per step, every formula of the proof in
backticks in Rocq syntax, and the rule or lemma used by each step.  It is
meant to be rewritten into fluent prose later (by hand or by an LLM), and
it is written in the Markdown format of [cyp](../cyp/README.md), so that
cyp can check it again.

```coq
From XText Require Import Explain.
Explain foo.                       (* prints the text *)
Explain foo to "examples/foo.md".  (* writes it to a file *)
```

Proofs ending with `Qed` work too: the body is read with
`coq.env.const-body`, which rocq-elpi 3.4.0 gives even for opaque
constants.

## Build

Rocq 9.1.1 and rocq-elpi 3.4.0 (opam switch `native`):

```sh
eval "$(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=native --set-switch)"
make          # builds Explain.vo, then paper.v, lemmas.v, inductive.v, which write examples/*.md
```

Files: `xtext.elpi` (the transducer), `Explain.v` (the command),
`paper.v` (the paper's examples), `lemmas.v` (small lemmas),
`inductive.v` (induction, case analysis, rewriting, fix), `examples/`
(the 24 texts produced), `cyp-check/` (cyp's results); see also
`thesis.v`, `stdlib.v` and `exp_examples.v` below (76 texts in all).

## The output

```markdown
---
require: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# or_commut

Let `A B : Prop`{.var}. Assume `A \/ B`{.hyp} (h). We prove `B \/ A`{.claim}.

- We prove `B \/ A`{.fact} by case analysis on `A \/ B`{.fact} (h) (or, or_ind):
- Case 1: we prove `A -> B \/ A`{.claim}.
  - Assume `A`{.hyp} (i).
    - By definition of or (or_intror), from `A`{.fact} (i) we deduce `B \/ A`{.claim} *by eapply @or_intror; eauto*.
- Case 2: we prove `B -> B \/ A`{.claim}.
  ...
- We have `B \/ A`{.claim} in all cases.
```

- the header is cyp's; `require` loads the file that defines the theorem;
- the abstractions at the top of the proof make the statement (`Let`,
  `Assume`, `We prove`);
- each formula carries its cyp role (`{.var}`, `{.hyp}`, `{.claim}`,
  `{.fact}`), so that cyp does not have to guess it from the words;
- a subproof is a list item: its conclusion, with the lines that lead to
  it indented below;
- each step names its rule or lemma; a theorem step carries `*by exact
  @T*`, a constructor step `*by eapply @K; eauto*`.

## Rules of the paper (TLCA 1995, section 3.1)

- **Rules for abstraction**, in their **iterated** form (a run of
  binders of the same kind gives one line):
  - `λl:A_Type. M` → `Let l : A` ... `We have proved τ`;
  - `λh:A_Prop. M` → `Assume A (h) and ...` ... `We have proved τ`;
  - `λx:A_Set. M` → `Let us consider an arbitrary x : A` ... `We have τ, since x is arbitrary`
    (several: `Let us choose arbitrarily ...` ... `Thus we have τ`).
- **Rules for application**, in their **iterated** form (arguments are
  cut into maximal runs of the same kind):
  - specialisation `M_{∀x:P.Q} N` → `M` then `In particular τ`;
  - modus ponens `M_{P⇒Q} N1..Nk` → `- N1 ... - Nk - M` then `We deduce τ`.
- **Rules for identifiers**: `h_τ` → `By h we have τ`; theorem `T_τ` →
  `Using T we get τ`.
- The **\* context** is used at the top of the proof, where the theorem
  is announced (the statement), and inside the cases (see below).
- Expressions that match no rule are **left unchanged**: `Using t we get τ`.

## Rules of the thesis (chapter 6, inductive constructions)

They replace the paper's rules for introduction and elimination theorems.

- **Constr** (6.2.1): a constructor is a definition step, not a theorem:
  `By definition of C (K), we have τ`.  When all its premises are
  hypotheses, it reads `By definition of C (K), from A (h) we deduce τ`
  (the thesis's `Par définition, de H0 nous déduisons B ∨ A`).  Otherwise
  the premises come first, as dashed subproofs.
- **ElimOpen / ElimCase / ElimClose** (6.2.2): an elimination
  `C_ind ... H` is read as a proof by cases, announced first, with the
  object eliminated: `We prove τ by case analysis on A ∨ B (h) (or,
  or_ind):`, then `Case 1: ...`, ..., then `We have τ in all cases`.
  Cases are numbered in Dewey notation (`Case 1.2:`).
- **One case** (6.3.1, `and`, `ex`): there is no case, only a return to
  the definition: `Going back to the definition of and (and_ind) in x ∧ y
  (h), we prove τ:` with the branch below it, and no closing sentence.
- **Zero cases** (6.3.2, `False`): `By contradiction (False, ...), from
  False (f) we can deduce τ`.
- **Dependent eliminations** (6.3.3, `bool`, `nat`): the goal is
  generalised before it is specialised: `To prove n + 0 = n by induction
  (nat, nat_ind), we generalise it to forall n0, n0 + 0 = n0:`, the cases,
  `These cases being exhaustive, we deduce ...`, then `In particular n + 0 = n`.
- **Eliminations with recursion** (6.3.4): a binder of a branch whose
  type mentions the motive is an induction hypothesis (`Assume by
  induction hypothesis m + 0 = m (IH)`).  The cases are marked `(base)` or
  `(inductive)`, and the proof is announced `by induction` instead of `by
  case analysis`.  All of this is read from the type of the elimination
  theorem, so it works for `nat_ind`, `list_ind`, `le_ind`, ...

## Departures from the paper and the thesis

- The shorter rule `We have h` for assumptions and the variants for
  applications to variables (`Using f with f1, f2 ...`) are not used: they
  drop formulas, and the text must keep all of them.
- The constructor and the elimination theorem are named (`(or_intror)`,
  `(nat_ind)`), which the thesis leaves out, so that the reader, or cyp,
  can check the step.
- A witness of a constructor is shown: `By definition of ex (ex_intro)
  with witness t` (the paper's `The element c proves τ`), since it is part
  of the proof.
- Each case states its goal (`Case 1: we prove τ1`), and its branch is
  read in the \* context (no `We have proved τ1` at its end), since the
  goal is already stated at the head of the case.
- The generalised predicate of a dependent elimination is written as a
  statement (`forall n0, ...`), not as a λ-term: it reads better and
  type-checks as a formula.
- `match` is read as an elimination (the thesis hides the primitive
  operator behind `C_ind`): first kind if the inductive type is in `Prop`,
  else second kind.  Elimination theorems are found by Rocq's naming
  scheme `C_ind` / `C_sind`, not by the shape of their type (6.4.2).
- **Rewriting** (`eq_ind`, `eq_ind_r`, `eq_rect`, ...): the thesis says
  (end of 6.4.2) that the generic text is poor and that a specific rule is
  needed, but gives none.  Here the proof of `P x` and the proof of the
  equation come first, as dashed subproofs, then `Rewriting with y = x
  from right to left (eq_ind_r), we get P y`.
- **`fix`** (not treated by the thesis; 6.3.4 studies only the types of
  elimination theorems): `We prove τ by recursion on n (fix f):` with the
  body below it.  A recursive call reads `By induction hypothesis (the
  recursive call f) we have τ`, and a `match` whose case calls `f` is an
  inductive case.  Nothing checks that the calls are on smaller
  arguments, since Rocq already did.
- The closing step of an elimination (`These cases being exhaustive, we
  deduce ...`, `We have τ in all cases`) gets a justification built from
  the elimination: `*by eapply (@T params motive); cbv beta; eauto*` for an
  elimination theorem `T`, which closes it from the case claims, and
  `*by destruct x; cbn; eauto*` for a `match` on a variable `x`.
- Intro patterns leave redexes `fun h => (fun i => M) h`; they are reduced
  and the user's name `i` is kept.  Other redexes are cuts and are
  rendered with the application rules.  Casts are skipped; `let x := N in
  M` is read as `(fun x => M) N`.
- A product `A -> Q` whose domain is not a proposition is read as a
  specialisation, not as a function application.
- Formulas are printed by Rocq, with notations.  A bound name that clashes
  with the context is renamed (`n0`), and anonymous hypotheses are called
  `h`.  An equality with a bare constructor on one side gets its type,
  `([]) = ([]) :> list A`, since `[] = []` does not type-check again.
- Markdown lists replace the paper's dashes; a subproof's lines come
  below its conclusion (indented), not above it.
- `Let us consider` / `Let us choose` instead of `Consider` / `Choose`, so
  that the line reads as a binder for cyp.

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

All 24 texts are generated (`examples/`).  cyp was run on 15 of them
(`cyp-check/`, with `CYP_ROCQ="rocq c -R /home/thery/git/coq_tmp/xtext
XText"` so that the `Require Import XText.<file>` of the header works):

| text | list items | proved | not proved | not checked |
|---|---|---|---|---|
| S_proof | 6 | 6 | 0 | 0 |
| imp_trans | 5 | 5 | 0 | 0 |
| eq_trans | 3 | 3 | 0 | 0 |
| bool_cases | 8 | 7 | 0 | 1 |
| add_0_r | 11 | 8 | 0 | 3 |
| plus_n_Sm | 11 | 8 | 0 | 3 |
| le_0_m | 8 | 5 | 0 | 3 |
| le_n_S | 8 | 5 | 0 | 3 |
| or_commut | 8 | 5 | 0 | 3 |
| or_swap | 8 | 5 | 0 | 3 |
| app_nil_r | 12 | 8 | 0 | 4 |
| praeclarum | 11 | 9 | 0 | 2 |
| nearly_reflexive | 11 | 9 | 0 | 2 |
| le_0_n_fix | 11 | 8 | 0 | 3 |
| length_app_fix | 15 | 9 | 1 | 5 |

- *Not checked*: lines with no claim (`Let`, `Assume`, the announcement
  of a case analysis) and the cases' own closing.
- `length_app_fix`: the red step is the recursive call, `By induction
  hypothesis (the recursive call length_app') we have ...`: it states
  the theorem itself, which cyp cannot prove without the fix.
- cyp proves each claim again with its own tactics, so a green step says
  that the claim follows, not that it follows the way the text says.

## The examples of the two theses (`thesis.v`)

The proof terms are written as close as possible to the λ-terms of the
theses.

**Tauto** (Coscoy, Fig. 1.5, 2.6, 2.8, 2.11): `fun A B C h1 h2 h3 => h3 h1 h2`.
- Same: the statement (`Let A B C`, `Assume A (h1) and B (h2) and A -> B -> C (h3)`).
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
- Already there: the type that a step proves is the one Rocq computes
  (`In particular R z y -> R y x -> R z x`, `We prove R z x`), so the
  unfolded form is shown, like the thesis's inherited types (3.3.2).
- Missing: the thesis's `ce qui est équivalent à`.  Fig. 5.11 says
  `Montrons (Trans E (Inv E R)), ce qui est équivalent à ∀x, y, z ...`
  and `Montrons (R z x), ce qui est équivalent à (Inv R x z)`.  xtext states
  the body's type `R z x` only, and never links `Trans E R` (from `By h`)
  to its unfolding `forall x y z, ...`: the δ-conversion is silent.  This
  is the "Cast'" of the thesis (5.2.2), queued as the next round.  Also
  missing: the specialisation `h z y x` is not said with the names of the
  instances (`En appliquant h à z, y, x, h2 et h1`).

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

Future work, not done: the text of an **incomplete proof** (section 3.3.3),
where each open goal is written `Prouvez G` at its place (`Supposons (x ⊃
z) ∧ (y ⊃ t) (1) / Supposons x ∧ y (2) / Prouvez z / Prouvez t / Ceci
réuni donne z ∧ t`).

## More examples: theses, Stdlib, CORE-MATH

Files: `thesis.v` (the theses' examples, above), `stdlib.v` (40 lemmas
of Rocq's Stdlib, explained from the library itself: `Time Explain
app_assoc to ...`), `exp_examples.v` (5 lemmas of the CORE-MATH exp
proof, read from its compiled `.vo` files, not in `make all`: `make
exp_examples.vo`).  `measure.sh f.v` prints, for each text, the time of
`Explain` (Rocq's `Time`), the number of list items and the size;
`cyprun.sh` and `cyprun_exp.sh` run cyp (300 s per text for the theses and
Stdlib, 600 s for CORE-MATH).  For the CORE-MATH texts, the header of the
copy checked by cyp also loads Reals, Flocq and the exp files: the header
written by xtext only requires the file of the theorem, and its notations
(`%R`) are then unknown.

`thesis.v`:

| example | items | chars | time (s) | cyp proved / not proved / not checked |
|---|---|---|---|---|
| Tauto | 4 | 417 | 0.025 | 4 / 0 / 0 |
| Trans_Inv | 5 | 561 | 0.01 | 5 / 0 / 0 |
| ABCD | 12 | 720 | 0.01 | 12 / 0 / 0 |
| or_com | 8 | 807 | 0.012 | 5 / 0 / 3 |
| or_sym_nd | 8 | 755 | 0.01 | 5 / 0 / 3 |
| praeclarum_nd | 17 | 1220 | 0.018 | 17 / 0 / 0 |
| ADD0 | 12 | 1163 | 0.019 | 9 / 0 / 3 |

`stdlib.v`:

| example | items | chars | time (s) | cyp proved / not proved / not checked |
|---|---|---|---|---|
| std_app_assoc | 38 | 3575 | 0.102 | 32 / 0 / 6 |
| std_app_nil_r | 30 | 2712 | 0.055 | 25 / 0 / 5 |
| std_app_comm_cons | 1 | 382 | 0.007 | 1 / 0 / 0 |
| std_rev_involutive | 15 | 1661 | 0.044 | 11 / 0 / 4 |
| std_rev_app_distr | 18 | 2186 | 0.018 | 14 / 0 / 4 |
| std_length_rev | 18 | 2232 | 0.015 | 1 / 13 / 4 |
| std_map_app | 15 | 1945 | 0.017 | 9 / 0 / 6 |
| std_map_map | 12 | 1802 | 0.014 | 8 / 0 / 4 |
| std_length_app | 16 | 1969 | 0.015 | 1 / 9 / 6 |
| std_in_app_or | 31 | 3278 | 0.042 | 18 / 1 / 12 |
| std_in_or_app | 69 | 5983 | 0.051 | 48 / 0 / 21 |
| std_in_map | 36 | 3149 | 0.026 | 23 / 0 / 13 |
| std_in_eq | 4 | 465 | 0.003 | 2 / 0 / 2 |
| std_in_cons | 4 | 453 | 0.004 | 1 / 0 / 3 |
| std_Nat_add_comm | 196 | 23612 | 0.159 | 81 / 107 / 8 |
| std_Nat_add_assoc | 265 | 33470 | 0.333 | 102 / 154 / 9 |
| std_Nat_mul_comm | 196 | 23620 | 0.23 | 81 / 107 / 8 |
| std_Nat_le_trans | 484 | 77260 | 0.499 | timeout (300s) |
| std_Nat_add_0_r | 138 | 15887 | 0.149 | 59 / 73 / 6 |
| std_Nat_add_succ_r | 202 | 24435 | 0.18 | 85 / 109 / 8 |
| std_Nat_le_refl | 19 | 1865 | 0.014 | 7 / 10 / 2 |
| std_Nat_lt_irrefl | 42 | 5456 | 0.032 | 30 / 9 / 3 |
| std_Nat_mul_1_r | 118 | 13560 | 0.112 | 41 / 73 / 4 |
| std_Nat_pred_succ | 1 | 288 | 0.003 | 1 / 0 / 0 |
| std_plus_n_O | 12 | 1142 | 0.008 | 9 / 0 / 3 |
| std_plus_n_Sm | 12 | 1293 | 0.009 | 9 / 0 / 3 |
| std_andb_comm | 16 | 1568 | 0.007 | 13 / 0 / 3 |
| std_orb_comm | 16 | 1563 | 0.007 | 13 / 0 / 3 |
| std_negb_involutive | 6 | 700 | 0.005 | 5 / 0 / 1 |
| std_andb_true_r | 6 | 676 | 0.003 | 5 / 0 / 1 |
| std_orb_false_r | 6 | 681 | 0.003 | 5 / 0 / 1 |
| std_andb_assoc | 36 | 3838 | 0.016 | 29 / 0 / 7 |
| std_negb_andb | 16 | 1785 | 0.008 | 13 / 0 / 3 |
| std_and_comm | 11 | 1078 | 0.147 | 7 / 0 / 4 |
| std_or_comm | 21 | 1559 | 0.01 | 13 / 0 / 8 |
| std_and_assoc | 21 | 1933 | 0.014 | 15 / 0 / 6 |
| std_or_assoc | 39 | 3098 | 0.02 | 25 / 0 / 14 |
| std_eq_sym | 2 | 425 | 0.003 | 2 / 0 / 0 |
| std_eq_trans | 2 | 399 | 0.003 | 2 / 0 / 0 |
| std_f_equal | 2 | 464 | 0.003 | 2 / 0 / 0 |

`exp_examples.v`:

| example | items | chars | time (s) | cyp proved / not proved / not checked |
|---|---|---|---|---|
| exp_round_one | 26 | 4370 | 0.037 | 5 / 15 / 6 |
| exp_succ_one | 13 | 2149 | 0.141 | 11 / 2 / 0 |
| exp_pred_x_small | 9 | 1837 | 0.311 | 8 / 1 / 0 |
| exp_grid_plus | 23 | 4903 | 0.037 | 7 / 9 / 7 |
| exp_rnd_same_half_cell | 379 | 90904 | 2.416 | timeout (600s) |

What breaks or becomes unreadable on the large ones:

- **Generated proofs are explained as they are.**  `Nat.add_comm`,
  `Nat.mul_comm`, ... are proved with setoid rewriting: their texts (200-480
  items) are mostly about `Morphisms.Proper`, `ProperProxy`,
  `RelationClasses.Reflexive`, the internals of `rewrite`, not about
  arithmetic.  The `lia`, `ring` and `interval` certificates of CORE-MATH
  appear as local definitions (`Let __ff be Tauto.IMPL (...)`,
  `RTautoChecker_sound` used 12 times in `rnd_same_half_cell`) and lines
  of 1500-2200 characters.  Recognising such subproofs and writing `by lia`
  is the tactic rule queued for the next round.
- **Implicit arguments.**  Rocq prints `Equivalence eq` or `length [] =
  0` without the type, and these formulas do not type-check again: cyp
  marks them as errors, and all the steps after them too.  This is most of
  the "not proved" of the `Nat.*` and `length_*` texts.  Dropping and
  keeping arguments by re-elaboration is queued too.
- **Local definitions** (`Let hyp_list be nil`) have no form in cyp, so a
  later formula that uses `hyp_list` is a Rocq error.
- **Size**: `Nat.le_trans` (484 items) and `rnd_same_half_cell` (379
  items, 91 000 characters) are generated in 0.5 s and 2.4 s, but cyp
  does not finish them within its limit (300 s and 600 s).

### Fixes to the transducer in this round

Each was needed by an example, and changes no rule of the paper or the
thesis:

- `tr` keeps its first answer and, when no rule applies to a subterm,
  shows it unchanged.  `Rnd.grid_plus` took more than 15 minutes because a
  failure deep in a `ring` certificate made the whole translation
  backtrack; it now takes 0.04 s.
- `let x := V in M` keeps `x` with its value in the context (before, it
  was read as `(fun x => M) V`, and types under `x` were no longer
  convertible: `rnd_same_half_cell` was left untranslated).  A local proof
  is now a cut: its subproof, named `(x)`, then the rest.  This changes
  the texts of `drinker` and `forall_and` (`destruct` on a term builds such
  a `let`): one level less, and the cases come right after the cut.
- The header also loads `Bool`, for the Stdlib boolean lemmas.
- The `destruct x` justification is used only when `x` is not a proof:
  cyp names hypotheses `H`, `H0`, ..., not as in the text (`or_sym_nd`).

Regression: all 24 earlier texts are generated, and cyp gives the same
counts as before on the 15 of `cyp-check/`.

## Not done

- The section "Further optimizations" of the paper (one-use
  assumptions, `Trivially`, `A fortiori`, dependence analysis).
- The specific wordings of the paper's figures for the usual connectives
  and classical reasoning (`Altogether`, `Obviously`, `If we have ...
  Otherwise`).
- From the thesis: leaving out the generalised predicate (6.4.1),
  elimination theorems recognised by the shape of their type (6.4.2), and
  its other chapters (type annotations, reversible scripts).
- Mutual fixpoints (`mfix`) and `cofix` are left unchanged, as are
  non-propositional subterms.
- The `require` line of the header is fixed (Arith, Lia, List and the
  file of the theorem); the load path for cyp must be given by `CYP_ROCQ`.
