[Back to the README of xtext](../README.md)

# Inferable arguments, tactics, unfolding

Four generic mechanisms, after Coscoy's thesis.  Each can be switched
off for measurements with the environment variable `XTEXT_OFF` (a
comma-separated list of `explicit`, `args`, `tactics`, `thatis`; and
`motive`, the motive of an elimination left out, thesis 6.4.1, see ["Rules
of the thesis"](rules.md#rules-of-the-thesis-chapter-6-inductive-constructions)).

## (3a) Formulas that type-check again (thesis 5.4, applied to formulas)

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
  with more than 60 such applications (`xtext-implicit-choice-limit`)
  is printed in full when the fast
  test fails.  The test is up to conversion and assumes that Rocq parses
  the printed text back to the skeleton (notations, scopes).
- Binder types (`Let`, `Assume`) and the local definitions get the same
  treatment.

## (3b) Inferable arguments of an application (thesis 5.4, the extended App)

A run of specialisations followed by a run of premises (`h z y x h2 h1`)
is written as one modus ponens step when the specialised arguments can be
inferred.  The test: the application with these arguments as holes
elaborates, against its type, back to the same term.  The step `In
particular R z y -> R y x -> R z x` then disappears.  Nothing is
dropped by name.

## (5) Tactic-built subproofs (thesis 5.4, the pragmatic method)

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

## (4) "that is" (thesis 3.3 and 5.2.2, Cast')

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

## Local definitions

`let u := e in M`, when `e` is not a proof, is now written *Let `u : T :=
e`* (role `{.var}`), the local definition of cyp, so that the steps after
it may use `u`.

## Measurements

All 76 texts, generated with each mechanism alone and with all of them
(measured before 6.4.1, the motive left out, which is not in the table)
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

Per text: items and characters with no mechanism and with all, and the
generation time with all (switch `native`).

| example | items none → all | chars none → all | time all (s) |
|---|---|---|---|
| identity | 1 → 1 | 272 → 272 | 0.04 |
| S_proof | 6 → 6 | 484 → 484 | 0.01 |
| or_intro_example | 2 → 2 | 475 → 475 | 0.01 |
| or_commut | 8 → 8 | 805 → 805 | 0.01 |
| le_0_m | 8 → 8 | 882 → 882 | 0.01 |
| praeclarum | 11 → 11 | 942 → 942 | 0.02 |
| nearly_reflexive | 11 → 9 | 1075 → 960 | 0.02 |
| drinker | 26 → 25 | 2387 → 2338 | 0.06 |
| and_swap | 3 → 3 | 525 → 525 | 0.04 |
| or_swap | 8 → 8 | 747 → 747 | 0.01 |
| imp_trans | 5 → 5 | 444 → 444 | 0.01 |
| not_not_intro | 4 → 4 | 375 → 404 | 0.01 |
| ex_forall | 7 → 7 | 881 → 881 | 0.03 |
| forall_and | 5 → 5 | 585 → 585 | 0.02 |
| add_0_r | 11 → 11 | 1110 → 1110 | 0.04 |
| le_add_r | 15 → 15 | 1594 → 1594 | 0.08 |
| double_neg_em | 9 → 9 | 715 → 787 | 0.01 |
| plus_n_Sm | 11 → 11 | 1295 → 1295 | 0.07 |
| app_nil_r | 12 → 12 | 1224 → 1236 | 0.05 |
| eq_trans | 3 → 3 | 437 → 437 | 0.02 |
| le_n_S | 8 → 8 | 992 → 992 | 0.07 |
| le_0_n_fix | 11 → 11 | 1048 → 1048 | 0.01 |
| length_app_fix | 15 → 14 | 1676 → 1552 | 0.04 |
| bool_cases | 8 → 8 | 977 → 977 | 0.01 |
| Tauto | 4 → 4 | 417 → 417 | 0.09 |
| Trans_Inv | 5 → 4 | 567 → 661 | 0.01 |
| ABCD | 12 → 12 | 720 → 720 | 0.01 |
| or_com | 8 → 8 | 807 → 807 | 0.01 |
| or_sym_nd | 8 → 8 | 755 → 755 | 0.01 |
| praeclarum_nd | 17 → 13 | 1296 → 1082 | 0.01 |
| ADD0 | 12 → 11 | 1182 → 1114 | 0.02 |
| std_app_assoc | 38 → 36 | 3632 → 3469 | 0.29 |
| std_app_nil_r | 30 → 28 | 2741 → 2633 | 0.11 |
| std_app_comm_cons | 1 → 1 | 380 → 426 | 0.01 |
| std_rev_involutive | 15 → 15 | 1651 → 1661 | 0.04 |
| std_rev_app_distr | 18 → 18 | 2222 → 2222 | 0.06 |
| std_length_rev | 18 → 18 | 2276 → 2286 | 0.07 |
| std_map_app | 15 → 15 | 1945 → 1945 | 0.05 |
| std_map_map | 12 → 12 | 1788 → 1793 | 0.04 |
| std_length_app | 16 → 15 | 1988 → 1908 | 0.04 |
| std_in_app_or | 31 → 31 | 3278 → 3278 | 0.21 |
| std_in_or_app | 69 → 18 | 5983 → 1755 | 0.08 |
| std_in_map | 36 → 36 | 3149 → 3149 | 0.08 |
| std_in_eq | 4 → 4 | 465 → 465 | 0.01 |
| std_in_cons | 4 → 4 | 453 → 453 | 0.01 |
| std_Nat_add_comm | 196 → 85 | 25194 → 11659 | 0.41 |
| std_Nat_add_assoc | 265 → 105 | 35634 → 15181 | 0.42 |
| std_Nat_mul_comm | 196 → 85 | 25202 → 11657 | 0.37 |
| std_Nat_le_trans | 484 → 112 | 80900 → 21247 | 0.51 |
| std_Nat_add_0_r | 138 → 104 | 16997 → 14066 | 0.45 |
| std_Nat_add_succ_r | 202 → 87 | 26069 → 12046 | 0.47 |
| std_Nat_le_refl | 19 → 16 | 1981 → 1784 | 0.04 |
| std_Nat_lt_irrefl | 42 → 35 | 5707 → 4457 | 0.12 |
| std_Nat_mul_1_r | 118 → 89 | 14492 → 12345 | 0.37 |
| std_Nat_pred_succ | 1 → 1 | 301 → 338 | 0.01 |
| std_plus_n_O | 12 → 11 | 1161 → 1093 | 0.02 |
| std_plus_n_Sm | 12 → 11 | 1312 → 1222 | 0.03 |
| std_andb_comm | 16 → 16 | 1568 → 1568 | 0.02 |
| std_orb_comm | 16 → 16 | 1563 → 1563 | 0.02 |
| std_negb_involutive | 6 → 6 | 700 → 700 | 0.01 |
| std_andb_true_r | 6 → 6 | 676 → 676 | 0.04 |
| std_orb_false_r | 6 → 6 | 681 → 681 | 0.01 |
| std_andb_assoc | 36 → 36 | 3838 → 3838 | 0.06 |
| std_negb_andb | 16 → 16 | 1785 → 1785 | 0.03 |
| std_and_comm | 11 → 11 | 1055 → 1091 | 0.02 |
| std_or_comm | 21 → 21 | 1536 → 1572 | 0.02 |
| std_and_assoc | 21 → 21 | 1898 → 1946 | 0.05 |
| std_or_assoc | 39 → 39 | 3063 → 3111 | 0.05 |
| std_eq_sym | 2 → 2 | 425 → 425 | 0.01 |
| std_eq_trans | 2 → 2 | 399 → 399 | 0.01 |
| std_f_equal | 2 → 2 | 464 → 464 | 0.01 |
