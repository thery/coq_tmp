---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} by recursion on `l1` (fix length_app'):
  - Let `A : Type`{.var}. Let `l1 l2 : list A`{.var}. We prove `length (l1 ++ l2) = length l1 + length l2` by induction on `l1` (list, match):
    - Case 1 (base): we prove `length ([] ++ l2) = length ([] ++ l2)`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `length ([] ++ l2) = length ([] ++ l2)`{.claim}.
    - Case 2 (inductive): we prove `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - Let `x : A`{.var}. Let `l : list A`{.var}.
        - By induction hypothesis (the recursive call length_app') we have `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
        - Using *f_equal*{.just} we get `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim}.

        By *congruence*{.just} we deduce `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.

    These cases being exhaustive, we deduce `length (l1 ++ l2) = length l1 + length l2`{.claim}.
