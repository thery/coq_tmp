---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_O

Let `n : nat`{.var}. We prove `n = n + 0`{.claim}.

- We prove `n = n + 0` by induction on `n` (nat, *nat_ind*{.just}):
  - Case 1 (base): we prove `0 = 0 + 0`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `0 = 0`{.claim}.
  - Case 2 (inductive): we prove `forall n0 : nat, n0 = n0 + 0 -> S n0 = S n0 + 0`{.claim}.
    - Let us choose arbitrarily `n0 : nat`{.var}. Assume `n0 = n0 + 0`{.hyp} (IHn).
      - By application, we have `n0 = n0 + 0 -> S n0 = S (n0 + 0)`{.claim}.
        - By application, we have `forall y : nat, n0 = y -> S n0 = S y`{.claim}.
          - By application, we have `forall x y : nat, x = y -> S x = S y`{.claim}.
            - By application, we have `forall (f : nat -> nat) (x y : nat), x = y -> f x = f y`{.claim}.
              - By *f_equal_nat*{.just} we have `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y`{.claim}.
              - The element `nat` belongs to `Type`.
            - The element `S` belongs to `nat -> nat`.
        - The element `n0 + 0` belongs to `nat`.
      - By *IHn*{.just} we have `n0 = n0 + 0`{.claim}.

      By application, we have `S n0 = S (n0 + 0)`{.claim}.

  These cases being exhaustive, we deduce `n = n + 0`{.claim}.
