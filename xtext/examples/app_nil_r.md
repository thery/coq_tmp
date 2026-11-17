---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# app_nil_r'

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `l ++ [] = l`{.claim}.

- To prove `l ++ [] = l`{.fact} by induction (list, list_ind), we generalise it to `forall l0 : list A, l0 ++ [] = l0`{.fact}:
- Case 1 (base): we prove `[] = (@nil A)`{.claim}.
  - By definition of eq (eq_refl), we have `[] = (@nil A)`{.claim} *by eapply @eq_refl; eauto*.
- Case 2 (inductive): we prove `forall (x : A) (l0 : list A), l0 ++ [] = l0 -> (x :: l0) ++ [] = x :: l0`{.claim}.
  - Let `x : A`{.var}.
  - Let `l0 : list A`{.var}.
  - Assume by induction hypothesis `l0 ++ [] = l0`{.hyp} (IH).
    - By definition of eq (eq_refl), we have `x :: l0 = x :: l0`{.claim} *by eapply @eq_refl; eauto*.
    - By IH we have `l0 ++ [] = l0`{.claim}.
    - Rewriting with `l0 ++ [] = l0`{.fact} from right to left (eq_ind_r), we get `x :: l0 ++ [] = x :: l0`{.claim}.
- These cases being exhaustive, we deduce `forall l0 : list A, l0 ++ [] = l0`{.claim} *by eapply (@list_ind (A) (fun l0 : list A => l0 ++ [] = l0)); cbv beta; eauto*.
- In particular `l ++ [] = l`{.claim}.
