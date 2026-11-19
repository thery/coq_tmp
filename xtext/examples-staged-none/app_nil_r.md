---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# app_nil_r'

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `l ++ [] = l`{.claim}.

- We prove `l ++ [] = l`{.fact} by induction on `l`{.fact} (list, list_ind):
- Case 1 (base): we prove `[] = (@nil A)`{.claim}.
  - By definition of eq (eq_refl), we have `[] = (@nil A)`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall (x : A) (l0 : list A), l0 ++ [] = l0 -> (x :: l0) ++ [] = x :: l0`{.claim}.
  - Let `x : A`{.var}.
    - Let `l0 : list A`{.var}.
      - Assume `l0 ++ [] = l0`{.hyp} (IH).
        - By definition of eq (eq_refl), we have `x :: l0 = x :: l0`{.claim} *by Corelib.Init.Logic.eq_refl*.
        - By IH we have `l0 ++ [] = l0`{.claim}.
        - Rewriting with `l0 ++ [] = l0`{.fact} from right to left (eq_ind_r), we get `x :: l0 ++ [] = x :: l0`{.claim}.
- These cases being exhaustive, we deduce `l ++ [] = l`{.claim} *by Corelib.Init.Datatypes.list_ind*.
