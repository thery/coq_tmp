---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Let `m : nat`{.var}. We prove `m + 0 = m`{.claim}.

- To prove `m + 0 = m`{.fact} by induction (nat, nat_ind), we generalise it to `forall n : nat, n + 0 = n`{.fact}:
- Case 1 (base): we prove `0 + 0 = 0 + 0`{.claim}.
  - By definition of eq (eq_refl), we have `0 + 0 = 0 + 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
  - Let us choose arbitrarily `m0 : nat`{.var}.
    - Assume `m0 + 0 = m0`{.hyp} (IH).
      - By application, we have `m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
        - By application, we have `forall y : nat, m0 + 0 = y -> S (m0 + 0) = S y`{.claim}.
          - By application, we have `forall x y : nat, x = y -> S x = S y`{.claim}.
            - By application, we have `forall (f : nat -> nat) (x y : nat), x = y -> f x = f y`{.claim}.
              - By application, we have `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y`{.claim}.
                - By f_equal we have `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim}.
                - The element `nat`{.fact} belongs to `Type`{.fact}.
              - The element `nat`{.fact} belongs to `Type`{.fact}.
            - The element `S`{.fact} belongs to `nat -> nat`{.fact}.
          - The element `m0 + 0`{.fact} belongs to `nat`{.fact}.
        - The element `m0`{.fact} belongs to `nat`{.fact}.
      - By IH we have `m0 + 0 = m0`{.claim}.
      - By application, we have `S (m0 + 0) = S m0`{.claim}.
- These cases being exhaustive, we deduce `forall n : nat, n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
- In particular `m + 0 = m`{.claim}.
