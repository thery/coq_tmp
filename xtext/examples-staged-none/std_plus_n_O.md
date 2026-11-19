---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_O

Let `n : nat`{.var}. We prove `n = n + 0`{.claim}.

- We prove `n = n + 0`{.fact} by induction on `n`{.fact} (nat, nat_ind):
- Case 1 (base): we prove `0 = 0 + 0`{.claim}.
  - By definition of eq (eq_refl), we have `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall n0 : nat, n0 = n0 + 0 -> S n0 = S n0 + 0`{.claim}.
  - Let us choose arbitrarily `n0 : nat`{.var}.
    - Assume `n0 = n0 + 0`{.hyp} (IHn).
      - By application, we have `n0 = n0 + 0 -> S n0 = S (n0 + 0)`{.claim}.
        - By application, we have `forall y : nat, n0 = y -> S n0 = S y`{.claim}.
          - By application, we have `forall x y : nat, x = y -> S x = S y`{.claim}.
            - By application, we have `forall (f : nat -> nat) (x y : nat), x = y -> f x = f y`{.claim}.
              - By f_equal_nat we have `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y`{.claim}.
              - The element `nat`{.fact} belongs to `Type`{.fact}.
            - The element `S`{.fact} belongs to `nat -> nat`{.fact}.
          - The element `n0`{.fact} belongs to `nat`{.fact}.
        - The element `n0 + 0`{.fact} belongs to `nat`{.fact}.
      - By IHn we have `n0 = n0 + 0`{.claim}.
      - By application, we have `S n0 = S (n0 + 0)`{.claim}.
- These cases being exhaustive, we deduce `n = n + 0`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
