---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} by recursion on `l1` (fix length_app'):
  - Let `A : Type`{.var} and `l1 l2 : list A`{.var}. We prove `length (l1 ++ l2) = length l1 + length l2` by induction on *l1*{.just} (*list*{.just}, *induction*{.just}):
    - Case 1 (base): we prove `length ([] ++ l2) = length ([] ++ l2)`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `length ([] ++ l2) = length ([] ++ l2)`{.claim}.
    - Case 2 (inductive): we prove `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
      - Let `x : A`{.var} and `l : list A`{.var}.
        - The element `nat` belongs to `Type`.
        - The element `nat` belongs to `Type`.
        - The element `S` belongs to `nat -> nat`.
        - The element `length (l ++ l2)` belongs to `nat`.
        - The element `length l + length l2` belongs to `nat`.
        - In particular `length (l ++ l2) = length l + length l2`{.claim}.
          - By induction hypothesis (the recursive call length_app') we have `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.

        Applying *f_equal*{.just}, we have `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.

    These cases being exhaustive, we deduce `length (l1 ++ l2) = length l1 + length l2`{.claim}.
