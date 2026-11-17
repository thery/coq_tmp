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
  else second kind.  Elimination theorems are found by the shape of
  their type (6.4.2, see below), not by their name.
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
- With "that is" (mechanism (4) below) and the inferable arguments (3b),
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
is written `Prouvez G` at its place, is now `Explain_partial` (below).

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

The sizes, times and cyp results of all texts are in the table of the next
section (columns "none" and "cyp before" are the state of this section).

What breaks or becomes unreadable on the large ones:

- **Generated proofs are explained as they are.**  `Nat.add_comm`,
  `Nat.mul_comm`, ... are proved with setoid rewriting: their texts (200-480
  items) are mostly about `Morphisms.Proper`, `ProperProxy`,
  `RelationClasses.Reflexive`, the internals of `rewrite`, not about
  arithmetic.  The `lia`, `ring` and `interval` certificates of CORE-MATH
  appear as local definitions (`Let __ff be Tauto.IMPL (...)`,
  `RTautoChecker_sound` used 12 times in `rnd_same_half_cell`) and lines
  of 1500-2200 characters.  Now partly handled, see "Tactic-built
  subproofs" below.
- **Implicit arguments.**  Rocq prints `Equivalence eq` or `length [] =
  0` without the type, and these formulas do not type-check again: cyp
  marks them as errors, and all the steps after them too.  This is most of
  the "not proved" of the `Nat.*` and `length_*` texts.  Now handled,
  see "Formulas that type-check again" below.
- **Local definitions** (`Let hyp_list be nil`) had no form in cyp, so a
  later formula that used `hyp_list` was a Rocq error.  They are now
  written as cyp's local definitions (below).
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

## Inferable arguments, tactics, unfolding

Four generic mechanisms, after Coscoy's thesis.  Each can be switched
off for measurements with the environment variable `XTEXT_OFF` (a
comma-separated list of `explicit`, `args`, `tactics`, `thatis`).

### (3a) Formulas that type-check again (thesis 5.4, applied to formulas)

Rocq's printer leaves out the implicit arguments, so `@eq (list A) []
[]` prints as `[] = []`, which does not type-check again.  For each
formula, xtext builds its *skeleton*: the implicit arguments of every
application become holes.  It elaborates the skeleton
(`coq.elaborate-skeleton`) and keeps the printed form only if the result
is ground and convertible to the formula.  Otherwise it decides
application by application, in the order of the term: the arguments of
an application are left out if the skeleton still elaborates back,
with the earlier applications as decided and the later ones written in
full.  The kept applications are printed `@f a1 .. an`, for example
`[] = (@nil A)` or `RelationClasses.Reflexive (@eq nat)`.

- Rocq's implicit status (`coq.arguments.implicit`) only says which
  arguments the printer can drop.  Re-elaboration decides which ones may
  stay dropped.
- Limits: a kept application under a binder cannot be put back into the
  printed text by the placeholder method used here, so the whole formula
  is printed with `Printing All` (`@eq nat (@length A ...)`).  A formula
  with more than 60 such applications is printed in full when the fast
  test fails.  The test is up to conversion and assumes that Rocq parses
  the printed text back to the skeleton (notations, scopes).
- Binder types (`Let`, `Assume`) and the local definitions get the same
  treatment.

### (3b) Inferable arguments of an application (thesis 5.4, the extended App)

A run of specialisations followed by a run of premises (`h z y x h2 h1`)
is written as one modus ponens step when the specialised arguments can be
inferred.  The test: the application with these arguments as holes
elaborates, against its type, back to the same term.  The step `In
particular R z y -> R y x -> R z x` then disappears.  Nothing is
dropped by name.

### (5) Tactic-built subproofs (thesis 5.4, the pragmatic method)

A proper subproof whose proof term has at least `xtext-threshold` nodes
(default 300) is first tried with the tactics of `xtext-tactic`, in
order, on its statement in its own context.  The defaults are
`tauto` then `lia`, each with a 2 s time limit.  The first tactic that
closes it gives one step, `We have P *by lia*`, instead of the walk
through the term.  The success of the tactic is the guarantee; no
constant is recognised by its name.

- Where: on every subproof but the whole proof (the body of the theorem,
  and the body of a cast or `let` that is the whole proof).  The size is
  that of the proof term, so the large terms built by `lia`, `ring` or
  setoid rewriting are the ones tried.  Short subproofs keep their text.
- Parameters, in the Elpi database `xtext.db` (`Explain.v`):
  `xtext-tactic Ltac Text` (an Ltac definition, and the text written after
  *by*), `xtext-threshold N`.  To add `lra`, write `Ltac my_lra := timeout
  2 lra.` then `Elpi Accumulate xtext.db lp:{{ xtext-tactic "my_lra" "lra".
  }}`.  To change the threshold, write `:before "xtext-threshold"
  xtext-threshold 50 :- !.`
- Limits: a subproof that a tactic closes loses its explanation, even if
  it was written by hand (e.g. the inductive step of `Nat.add_assoc` at a
  lower threshold).  The threshold is the only control.  Tactics are run
  in Explain's environment; one not loaded there must be added as above.

### (4) "that is" (thesis 3.3 and 5.2.2, Cast')

When the type a subproof proves (synthesised) differs syntactically
from the type expected at its place (inherited) but Rocq finds them
convertible (`coq.unify-eq`), its conclusion says both: `By h2 we have Inv
E R y z, that is R z y`.  The expected types come from the type of the
function applied (premises of an application, of a constructor) and from
the declared type of the theorem for the whole proof.  The statement now
shows the declared type (`We prove Inv E R x z`, not `R z x`).  A
function whose type is a product only after unfolding gets the unfolded
type too (`By h we have Trans E R, that is forall x0 y0 z0 : E, ...`).
This is any definition, with no list of names.  With it, `Trans_Inv`
reads as Fig. 3.13 of the thesis.

- Limits: the cases of an elimination and the branches of a `match` do
  not get it (their goals are stated from the eliminator).  Many "that is"
  in the setoid-rewriting proofs (`Proper ...`, that is `forall x y, ...`)
  are true but noisy.

### Local definitions

`let u := e in M`, when `e` is not a proof, is now written *Let `u : T :=
e`* (role `{.var}`), the local definition of cyp, so that the steps after
it may use `u`.

### Measurements

All 76 texts, generated with each mechanism alone and with all of them
(`XTEXT_OFF`; generation time is the sum of Rocq's `Time` over the texts):

| mechanisms on | list items | characters | generation time (s) |
|---|---|---|---|
| none | 2916 | 418139 | 11.6 |
| formulas that type-check (3a) | 2916 | 426998 | 14.8 |
| inferable arguments (3b) | 2429 | 346399 | 8.1 |
| tactics (5) | 2163 | 310935 | 14.7 |
| "that is" (4) | 2916 | 431659 | 10.1 |
| all | 1856 | 278197 | 16.1 |

The tactics and the inferable arguments shorten the texts (by 26 % and
17 % in items); the formulas that type-check and "that is" make them
longer (by 2 % and 3 % in characters).  With all four, the texts have
36 % fewer items.  All 76 texts are still generated, in 16 s in all.

Per text: items and characters with no mechanism and with all; cyp
(proved / not proved / not checked), before (previous section) and after.
The texts were checked with a time limit of 300 s each.  `Nat.le_trans`
and `rnd_same_half_cell` time out both before and after (484 → 112 and
379 → 335 items).  A few texts not checked in the previous rounds are
"not run" before.

| example | items none → all | chars none → all | time all (s) | cyp before | cyp after |
|---|---|---|---|---|---|
| identity | 1 → 1 | 272 → 272 | 0.04 | not run | 1 / 0 / 0 |
| S_proof | 6 → 6 | 484 → 484 | 0.01 | 6 / 0 / 0 | 6 / 0 / 0 |
| or_intro_example | 2 → 2 | 475 → 475 | 0.01 | not run | 2 / 0 / 0 |
| or_commut | 8 → 8 | 805 → 805 | 0.01 | 5 / 0 / 3 | 5 / 0 / 3 |
| le_0_m | 8 → 8 | 882 → 882 | 0.01 | 5 / 0 / 3 | 5 / 0 / 3 |
| praeclarum | 11 → 11 | 942 → 942 | 0.02 | 9 / 0 / 2 | 9 / 0 / 2 |
| nearly_reflexive | 11 → 9 | 1075 → 960 | 0.02 | 9 / 0 / 2 | 7 / 0 / 2 |
| drinker | 26 → 25 | 2387 → 2338 | 0.06 | not run | 18 / 0 / 7 |
| and_swap | 3 → 3 | 525 → 525 | 0.04 | not run | 2 / 0 / 1 |
| or_swap | 8 → 8 | 747 → 747 | 0.01 | 5 / 0 / 3 | 5 / 0 / 3 |
| imp_trans | 5 → 5 | 444 → 444 | 0.01 | 5 / 0 / 0 | 5 / 0 / 0 |
| not_not_intro | 4 → 4 | 375 → 404 | 0.01 | not run | 3 / 0 / 1 |
| ex_forall | 7 → 7 | 881 → 881 | 0.03 | not run | 4 / 0 / 3 |
| forall_and | 5 → 5 | 585 → 585 | 0.02 | not run | 4 / 0 / 1 |
| add_0_r | 11 → 11 | 1110 → 1110 | 0.04 | 8 / 0 / 3 | 8 / 0 / 3 |
| le_add_r | 15 → 15 | 1594 → 1594 | 0.08 | not run | 12 / 0 / 3 |
| double_neg_em | 9 → 9 | 715 → 787 | 0.01 | not run | 7 / 0 / 2 |
| plus_n_Sm | 11 → 11 | 1295 → 1295 | 0.07 | 8 / 0 / 3 | 8 / 0 / 3 |
| app_nil_r | 12 → 12 | 1224 → 1236 | 0.05 | 8 / 0 / 4 | 8 / 0 / 4 |
| eq_trans | 3 → 3 | 437 → 437 | 0.02 | 3 / 0 / 0 | 3 / 0 / 0 |
| le_n_S | 8 → 8 | 992 → 992 | 0.07 | 5 / 0 / 3 | 5 / 0 / 3 |
| le_0_n_fix | 11 → 11 | 1048 → 1048 | 0.01 | 8 / 0 / 3 | 8 / 0 / 3 |
| length_app_fix | 15 → 14 | 1676 → 1552 | 0.04 | 9 / 1 / 5 | 8 / 1 / 5 |
| bool_cases | 8 → 8 | 977 → 977 | 0.01 | 7 / 0 / 1 | 7 / 0 / 1 |
| Tauto | 4 → 4 | 417 → 417 | 0.09 | 4 / 0 / 0 | 4 / 0 / 0 |
| Trans_Inv | 5 → 4 | 567 → 661 | 0.01 | 5 / 0 / 0 | 4 / 0 / 0 |
| ABCD | 12 → 12 | 720 → 720 | 0.01 | 12 / 0 / 0 | 12 / 0 / 0 |
| or_com | 8 → 8 | 807 → 807 | 0.01 | 5 / 0 / 3 | 5 / 0 / 3 |
| or_sym_nd | 8 → 8 | 755 → 755 | 0.01 | 5 / 0 / 3 | 5 / 0 / 3 |
| praeclarum_nd | 17 → 13 | 1296 → 1082 | 0.01 | 17 / 0 / 0 | 13 / 0 / 0 |
| ADD0 | 12 → 11 | 1182 → 1114 | 0.02 | 9 / 0 / 3 | 8 / 0 / 3 |
| std_app_assoc | 38 → 36 | 3632 → 3469 | 0.29 | 32 / 0 / 6 | 30 / 0 / 6 |
| std_app_nil_r | 30 → 28 | 2741 → 2633 | 0.11 | 25 / 0 / 5 | 23 / 0 / 5 |
| std_app_comm_cons | 1 → 1 | 380 → 426 | 0.01 | 1 / 0 / 0 | 1 / 0 / 0 |
| std_rev_involutive | 15 → 15 | 1651 → 1661 | 0.04 | 11 / 0 / 4 | 11 / 0 / 4 |
| std_rev_app_distr | 18 → 18 | 2222 → 2222 | 0.06 | 14 / 0 / 4 | 14 / 0 / 4 |
| std_length_rev | 18 → 18 | 2276 → 2286 | 0.07 | 1 / 13 / 4 | 14 / 0 / 4 |
| std_map_app | 15 → 15 | 1945 → 1945 | 0.05 | 9 / 0 / 6 | 9 / 0 / 6 |
| std_map_map | 12 → 12 | 1788 → 1793 | 0.04 | 8 / 0 / 4 | 8 / 0 / 4 |
| std_length_app | 16 → 15 | 1988 → 1908 | 0.04 | 1 / 9 / 6 | 9 / 0 / 6 |
| std_in_app_or | 31 → 31 | 3278 → 3278 | 0.21 | 18 / 1 / 12 | 18 / 1 / 12 |
| std_in_or_app | 69 → 18 | 5983 → 1755 | 0.08 | 48 / 0 / 21 | 10 / 0 / 8 |
| std_in_map | 36 → 36 | 3149 → 3149 | 0.08 | 23 / 0 / 13 | 23 / 0 / 13 |
| std_in_eq | 4 → 4 | 465 → 465 | 0.01 | 2 / 0 / 2 | 2 / 0 / 2 |
| std_in_cons | 4 → 4 | 453 → 453 | 0.01 | 1 / 0 / 3 | 1 / 0 / 3 |
| std_Nat_add_comm | 196 → 85 | 25194 → 11659 | 0.41 | 81 / 107 / 8 | 80 / 1 / 4 |
| std_Nat_add_assoc | 265 → 105 | 35634 → 15181 | 0.42 | 102 / 154 / 9 | 100 / 1 / 4 |
| std_Nat_mul_comm | 196 → 85 | 25202 → 11657 | 0.37 | 81 / 107 / 8 | 80 / 1 / 4 |
| std_Nat_le_trans | 484 → 112 | 80900 → 21247 | 0.51 | timeout | timeout |
| std_Nat_add_0_r | 138 → 104 | 16997 → 14066 | 0.45 | 59 / 73 / 6 | 95 / 3 / 6 |
| std_Nat_add_succ_r | 202 → 87 | 26069 → 12046 | 0.47 | 85 / 109 / 8 | 82 / 1 / 4 |
| std_Nat_le_refl | 19 → 16 | 1981 → 1784 | 0.04 | 7 / 10 / 2 | 14 / 0 / 2 |
| std_Nat_lt_irrefl | 42 → 35 | 5707 → 4457 | 0.12 | 30 / 9 / 3 | 32 / 0 / 3 |
| std_Nat_mul_1_r | 118 → 89 | 14492 → 12345 | 0.37 | 41 / 73 / 4 | 85 / 0 / 4 |
| std_Nat_pred_succ | 1 → 1 | 301 → 338 | 0.01 | 1 / 0 / 0 | 1 / 0 / 0 |
| std_plus_n_O | 12 → 11 | 1161 → 1093 | 0.02 | 9 / 0 / 3 | 8 / 0 / 3 |
| std_plus_n_Sm | 12 → 11 | 1312 → 1222 | 0.03 | 9 / 0 / 3 | 8 / 0 / 3 |
| std_andb_comm | 16 → 16 | 1568 → 1568 | 0.02 | 13 / 0 / 3 | 13 / 0 / 3 |
| std_orb_comm | 16 → 16 | 1563 → 1563 | 0.02 | 13 / 0 / 3 | 13 / 0 / 3 |
| std_negb_involutive | 6 → 6 | 700 → 700 | 0.01 | 5 / 0 / 1 | 5 / 0 / 1 |
| std_andb_true_r | 6 → 6 | 676 → 676 | 0.04 | 5 / 0 / 1 | 5 / 0 / 1 |
| std_orb_false_r | 6 → 6 | 681 → 681 | 0.01 | 5 / 0 / 1 | 5 / 0 / 1 |
| std_andb_assoc | 36 → 36 | 3838 → 3838 | 0.06 | 29 / 0 / 7 | 29 / 0 / 7 |
| std_negb_andb | 16 → 16 | 1785 → 1785 | 0.03 | 13 / 0 / 3 | 13 / 0 / 3 |
| std_and_comm | 11 → 11 | 1055 → 1091 | 0.02 | 7 / 0 / 4 | 7 / 0 / 4 |
| std_or_comm | 21 → 21 | 1536 → 1572 | 0.02 | 13 / 0 / 8 | 13 / 0 / 8 |
| std_and_assoc | 21 → 21 | 1898 → 1946 | 0.05 | 15 / 0 / 6 | 15 / 0 / 6 |
| std_or_assoc | 39 → 39 | 3063 → 3111 | 0.05 | 25 / 0 / 14 | 22 / 3 / 14 |
| std_eq_sym | 2 → 2 | 425 → 425 | 0.01 | 2 / 0 / 0 | 2 / 0 / 0 |
| std_eq_trans | 2 → 2 | 399 → 399 | 0.01 | 2 / 0 / 0 | 2 / 0 / 0 |
| std_f_equal | 2 → 2 | 464 → 464 | 0.01 | 2 / 0 / 0 | 2 / 0 / 0 |
| exp_round_one | 26 → 21 | 4338 → 3547 | 0.07 | 5 / 15 / 6 | 7 / 8 / 6 |
| exp_succ_one | 13 → 12 | 2184 → 2070 | 0.16 | 11 / 2 / 0 | 10 / 2 / 0 |
| exp_pred_x_small | 9 → 9 | 1883 → 1835 | 0.40 | 8 / 1 / 0 | 8 / 1 / 0 |
| exp_grid_plus | 23 → 23 | 4889 → 5003 | 0.31 | 7 / 9 / 7 | 7 / 9 / 7 |
| exp_rnd_same_half_cell | 379 → 335 | 90602 → 84057 | 9.64 | timeout | timeout |


Over the 65 texts checked both before and after, cyp proves 1084 steps
(1036 before) and fails on 32 (693 before); 222 are not checked (252).  The
failures before were mostly formulas that did not type-check again (`length
[] = 0`, `Equivalence eq`) and the steps after them; after, most of the
`Nat.*` failures are gone (`Nat.add_comm`: 107 → 1).  What remains:

- `std_or_assoc` (3, was 0) and the CORE-MATH texts: steps whose claim is
  true but that cyp's default tactics do not prove in their time limit;
- `length_app_fix` (1): the recursive call, as before;
- the CORE-MATH certificates that are not closed by `tauto` or `lia`
  (`lra`, `field`, `interval` are not among the default tactics).

Also fixed in this round: the `*by exact @T*` of a theorem uses its full
name (`@Stdlib.Classes.Morphisms.eq_proper_proxy`), which needs only
that its library be loaded, not imported.

## Contraction, eliminations by their type, proofs in progress

### (2) Contraction of application steps (thesis 3.4.2, Fig. 3.11-3.13)

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
  accepted configuration becomes the step's justification (`We deduce C
  *by auto*`), so that cyp runs the same tactic.  (2) Its line has no "that
  is", so
  no conversion step is hidden (the thesis's guarded contraction keeps the
  type expressions that belong to a conversion, Fig. 3.13).

Parameters, in `xtext.db`: `xtext-contraction "none" | "guarded" |
"maximal"` (the variable `XTEXT_CONTRACTION` overrides it) and
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

### (6) Elimination principles recognised by their type (thesis 6.4.2)

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

### (8) Proofs in progress (L. Théry's thesis, 3.3.3)

`Explain_partial.` (or `Explain_partial to "f.md".`), inside a proof,
prints the text of the proof so far.  Each open goal is written `Prove
G` at its place, as the thesis's `Prouvez G`.  The open goals are the holes
of the partial proof term; their statements are their types.

Limit: rocq-elpi gives the partial proof term only to a command that
closes the proof, so `Explain_partial` ends the proof, as `Abort` does.
In an editor, undo it to go on.

Tests (`partial.v`, texts `examples/*_partial*.md`):
- `or_swap_partial`, after `destruct`: two cases, each `Prove B \/ A`;
- `add_0_r_partial`, after `induction` and the base case: the inductive
  case is `Prove S m + 0 = S m`;
- `praeclarum_partial1` and `2`, the session of section 3.3.3: after
  `split`, `Prove z` and `Prove t`, then `So by definition of and (conj)`,
  as the thesis's `Prouvez z / Prouvez t / Ceci réuni donne z ∧ t`.  After
  the first conjunct, `We deduce z` (from `Hx` and `Hxz`) and `Prove t`.

### Measurements

All 78 texts (the 76 earlier ones and the two of `elim_type.v`), with each
contraction strategy.  The generation time is the sum of Rocq's `Time`
over the texts; the guard costs it.

| strategy | list items | characters | generation time (s) |
|---|---|---|---|
| none | 1919 | 288045 | 13.6 |
| maximal | 1720 | 267311 | 13.6 |
| guarded | 1818 | 279926 | 33.5 |

Texts that change, with cyp (proved / not proved / not checked; 300 s
per text).  "cyp none" is the previous round.  "= guarded" means the
maximal text has the same structure as the guarded one.

| example | items none / maximal / guarded | chars none → guarded | cyp none | cyp maximal | cyp guarded |
|---|---|---|---|---|---|
| S_proof | 6 / 5 / 5 | 484 → 466 | 6 / 0 / 0 | = guarded | 5 / 0 / 0 |
| nearly_reflexive | 9 / 8 / 8 | 960 → 936 | 7 / 0 / 2 | = guarded | 5 / 1 / 2 (†) |
| imp_trans | 5 / 4 / 4 | 444 → 426 | 5 / 0 / 0 | = guarded | 4 / 0 / 0 |
| length_app_fix | 14 / 13 / 13 | 1552 → 1495 | 8 / 1 / 5 | = guarded | 7 / 1 / 5 |
| ABCD | 12 / 9 / 9 | 720 → 638 | 12 / 0 / 0 | = guarded | 9 / 0 / 0 |
| praeclarum_nd | 13 / 11 / 11 | 1082 → 1042 | 13 / 0 / 0 | = guarded | 11 / 0 / 0 |
| std_app_assoc | 36 / 35 / 35 | 3469 → 3382 | 30 / 0 / 6 | = guarded | 29 / 0 / 6 |
| std_app_nil_r | 28 / 27 / 27 | 2633 → 2552 | 23 / 0 / 5 | = guarded | 22 / 0 / 5 |
| std_length_app | 15 / 14 / 14 | 1908 → 1849 | 9 / 0 / 6 | = guarded | 8 / 0 / 6 |
| std_in_map | 36 / 34 / 34 | 3149 → 3045 | 23 / 0 / 13 | = guarded | 21 / 0 / 13 |
| std_Nat_add_comm | 85 / 66 / 75 | 11659 → 10948 | 80 / 1 / 4 | 59 / 3 / 4 | 67 / 4 / 4 (†) |
| std_Nat_add_assoc | 105 / 82 / 93 | 15181 → 14188 | 100 / 1 / 4 | 75 / 3 / 4 | 83 / 6 / 4 (†) |
| std_Nat_mul_comm | 85 / 66 / 75 | 11657 → 10946 | 80 / 1 / 4 | 59 / 3 / 4 | 67 / 4 / 4 (†) |
| std_Nat_le_trans | 112 / 73 / 110 | 21247 → 21059 | timeout | = guarded | timeout |
| std_Nat_add_0_r | 104 / 82 / 91 | 14066 → 13115 | 95 / 3 / 6 | 73 / 3 / 6 | 79 / 6 / 6 (†) |
| std_Nat_add_succ_r | 87 / 68 / 75 | 12046 → 11167 | 82 / 1 / 4 | 61 / 3 / 4 | 66 / 5 / 4 (†) |
| std_Nat_le_refl | 16 / 15 / 15 | 1784 → 1730 | 14 / 0 / 2 | = guarded | 13 / 0 / 2 |
| std_Nat_lt_irrefl | 35 / 28 / 32 | 4457 → 4298 | 32 / 0 / 3 | 25 / 0 / 3 | 28 / 1 / 3 (†) |
| std_Nat_mul_1_r | 89 / 70 / 80 | 12345 → 11719 | 85 / 0 / 4 | 66 / 0 / 4 | 74 / 2 / 4 (†) |
| half_le | 36 / 29 / 30 | 6438 → 5345 | not run | = guarded | 19 / 4 / 6 (†) |
| even_or_odd | 27 / 27 / 27 | 3410 → 3410 | not run | = guarded | 19 / 0 / 8 |
| exp_round_one | 21 / 19 / 19 | 3547 → 3293 | 7 / 8 / 6 | = guarded | 8 / 5 / 6 |
| exp_succ_one | 12 / 11 / 11 | 2070 → 2023 | 10 / 2 / 0 | = guarded | 10 / 1 / 0 |
| exp_grid_plus | 23 / 22 / 23 | 5003 → 5003 | 7 / 9 / 7 | 7 / 8 / 7 | 7 / 9 / 7 |
| exp_rnd_same_half_cell | 335 / 329 / 329 | 84057 → 83174 | timeout | = guarded | timeout |


- Over the 66 texts checked both before and after (guarded): 25 steps not
  proved before, 21 after, for fewer steps (576 proved before, 563
  after, since steps were merged).
- With `maximal`, the 8 `Nat.*` texts and `grid_plus` lose more steps
  (561 → 425 proved) and keep slightly more failures (16 → 23): a
  contracted step that cyp's tactics cannot close becomes one more red
  step.  This is why `guarded` is the default.
- (†) These 9 texts changed after a last fix of the guard (the head of a
  modus ponens claimed the type of the bare function, not of its
  instance).  They could not be checked again: cyp was being rebuilt in
  the meantime (the new driver needs its compiled library, `CYP_LIB`),
  so their guarded results are those of the version before the fix.
- `Nat.le_trans` and `rnd_same_half_cell` time out in cyp, as before.

The texts in progress (`*_partial*.md`) have one `Prove G` step per open
goal.  They are not counted above.

## Not done

- The section "Further optimizations" of the paper (one-use
  assumptions, `Trivially`, `A fortiori`, dependence analysis).
- The specific wordings of the paper's figures for the usual connectives
  and classical reasoning (`Altogether`, `Obviously`, `If we have ...
  Otherwise`).
- From the thesis: leaving out the generalised predicate (6.4.1), and
  its other chapters (type annotations, reversible scripts).
- Mutual fixpoints (`mfix`) and `cofix` are left unchanged, as are
  non-propositional subterms.
- The `require` line of the header is fixed (Arith, Lia, List and the
  file of the theorem); the load path for cyp must be given by `CYP_ROCQ`.
