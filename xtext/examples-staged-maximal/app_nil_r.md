---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# app_nil_r'

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `l ++ [] = l`{.claim}.

- We prove `l ++ [] = l` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - Case 1 (base): we prove `[] = (@nil A)`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `[] = (@nil A)`{.claim}.
  - Case 2 (inductive): we prove `forall (x : A) (l0 : list A), l0 ++ [] = l0 -> (x :: l0) ++ [] = x :: l0`{.claim}.
    - Let `x : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `l0 ++ [] = l0`{.hyp} (IH).
      - By definition of eq (*eq_refl*{.just}), we have `x :: l0 = x :: l0`{.claim}.
      - By *IH*{.just} we have `l0 ++ [] = l0`{.claim}.

      Rewriting with `l0 ++ [] = l0`{.fact} from right to left (eq_ind_r), we get `x :: l0 ++ [] = x :: l0`{.claim}.

  These cases being exhaustive, we deduce `l ++ [] = l`{.claim}.
