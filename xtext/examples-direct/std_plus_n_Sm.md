---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm

Let `n m : nat`{.var}. We prove `S (n + m) = n + S m`{.claim}.

- We prove `S (n + m) = n + S m`{.fact} by induction on `n`{.fact} (nat, nat_ind):
- Case 1 (base): we prove `S (0 + m) = 0 + S m`{.claim}.
  - By definition of eq (eq_refl), we have `S m = S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
  - Let us consider an arbitrary `n0 : nat`{.var}.
    - Assume by induction hypothesis `S (n0 + m) = n0 + S m`{.hyp} (IHn).
      - By IHn we have `S (n0 + m) = n0 + S m`{.claim}.
      - Using f_equal_nat we get `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y`{.claim} *by Corelib.Init.Peano.f_equal_nat*.
      - We deduce `S (S (n0 + m)) = S (n0 + S m)`{.claim}.
- These cases being exhaustive, we deduce `S (n + m) = n + S m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
