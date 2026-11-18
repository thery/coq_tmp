---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# length_app'

We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim}.

- We prove `forall (A : Type) (l1 l2 : list A), length (l1 ++ l2) = length l1 + length l2`{.claim} by recursion on `l1`{.fact} (fix length_app'):
  - Let `A : Type`{.var}.
    - Let `l1 : list A`{.var}.
      - Let `l2 : list A`{.var}.
        - We prove `length (l1 ++ l2) = length l1 + length l2`{.fact} by induction on `l1`{.fact} (list, match):
        - Case 1 (base): we prove `length ([] ++ l2) = length ([] ++ l2)`{.claim}.
          - By definition of eq (eq_refl), we have `length ([] ++ l2) = length ([] ++ l2)`{.claim} *by Corelib.Init.Logic.eq_refl*.
        - Case 2 (inductive): we prove `A -> forall l : list A, S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
          - Let `x : A`{.var}.
            - Let `l : list A`{.var}.
              - By application, we have `length (l ++ l2) = length l + length l2 -> S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
                - By application, we have `forall y : nat, length (l ++ l2) = y -> S (length (l ++ l2)) = S y`{.claim}.
                  - By application, we have `forall x0 y : nat, x0 = y -> S x0 = S y`{.claim}.
                    - By application, we have `forall (f : nat -> nat) (x0 y : nat), x0 = y -> f x0 = f y`{.claim}.
                      - By application, we have `forall (B : Type) (f : nat -> B) (x0 y : nat), x0 = y -> f x0 = f y`{.claim}.
                        - By f_equal we have `forall (A0 B : Type) (f : A0 -> B) (x0 y : A0), x0 = y -> f x0 = f y`{.claim}.
                        - The element `nat`{.fact} belongs to `Type`{.fact}.
                      - The element `nat`{.fact} belongs to `Type`{.fact}.
                    - The element `S`{.fact} belongs to `nat -> nat`{.fact}.
                  - The element `length (l ++ l2)`{.fact} belongs to `nat`{.fact}.
                - The element `length l + length l2`{.fact} belongs to `nat`{.fact}.
              - In particular `length (l ++ l2) = length l + length l2`{.claim}.
                - By induction hypothesis (the recursive call length_app') we have `forall (A0 : Type) (l10 l20 : list A0), length (l10 ++ l20) = length l10 + length l20`{.claim}.
              - By application, we have `S (length (l ++ l2)) = S (length l + length l2)`{.claim}.
        - These cases being exhaustive, we deduce `length (l1 ++ l2) = length l1 + length l2`{.claim}.
