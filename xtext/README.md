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
(the 24 texts produced), `cyp-check/` (cyp's results).

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
- A case analysis on a variable `b` gets the justification `*by
  destruct b; assumption*`, so that cyp can close it.
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
| add_0_r | 11 | 5 | 0 | 6 |
| plus_n_Sm | 11 | 5 | 0 | 6 |
| le_0_m | 8 | 4 | 0 | 4 |
| le_n_S | 8 | 4 | 0 | 4 |
| or_commut | 8 | 3 | 0 | 5 |
| or_swap | 8 | 3 | 0 | 5 |
| app_nil_r | 12 | 3 | 2 | 7 |
| praeclarum | 11 | 1 | 0 | 10 |
| nearly_reflexive | 11 | 1 | 0 | 10 |
| le_0_n_fix | 11 | 1 | 0 | 10 |
| length_app_fix | 15 | 0 | 10 | 5 |

- *Not checked*: steps under an `Assume` or a `Let` inside the proof.  cyp
  has hypotheses and variables only in the statement.
- `app_nil_r`: the inductive case and the closing step are true, but
  cyp's tactics (`tauto | congruence | lia | firstorder | auto`) do not
  prove them: they need `simpl` or an induction.
- `length_app_fix`: the body of the fix starts with `Let A` and
  `Let l1 l2`, and the cases that follow mention `l2`, a variable cyp does
  not know, so Rocq gives errors.  This is the same limit of cyp as above,
  made visible.
- cyp proves each claim again with its own tactics, so a green step says
  that the claim follows, not that it follows the way the text says.

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
