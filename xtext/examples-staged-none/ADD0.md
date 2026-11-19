---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis.
by: tauto | congruence | lia | firstorder | auto
---

# ADD0

Let `m : nat`{.var}. We prove `m + 0 = m`{.claim}.

- We prove `m + 0 = m` by induction on `m` (nat, *nat_ind*{.just}):
  - Case 1 (base): we prove `0 + 0 = 0 + 0`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `0 + 0 = 0 + 0`{.claim}.
  - Case 2 (inductive): we prove `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
    - Let us choose arbitrarily `m0 : nat`{.var}. Assume `m0 + 0 = m0`{.hyp} (IH).
      - By application, we have `m0 + 0 = m0 -> S (m0 + 0) = S m0`{.claim}.
        - By application, we have `forall y : nat, m0 + 0 = y -> S (m0 + 0) = S y`{.claim}.
          - By application, we have `forall x y : nat, x = y -> S x = S y`{.claim}.
            - By application, we have `forall (f : nat -> nat) (x y : nat), x = y -> f x = f y`{.claim}.
              - By application, we have `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y`{.claim}.
                - By *f_equal*{.just} we have `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y`{.claim}.
                - The element `nat` belongs to `Type`.
              - The element `nat` belongs to `Type`.
            - The element `S` belongs to `nat -> nat`.
          - The element `m0 + 0` belongs to `nat`.
      - By *IH*{.just} we have `m0 + 0 = m0`{.claim}.

      By application, we have `S (m0 + 0) = S m0`{.claim}.

  These cases being exhaustive, we deduce `m + 0 = m`{.claim}.
