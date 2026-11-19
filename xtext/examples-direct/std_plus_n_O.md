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
  - Let us consider an arbitrary `n0 : nat`{.var}.
    - Assume by induction hypothesis `n0 = n0 + 0`{.hyp} (IHn).
      - By IHn we have `n0 = n0 + 0`{.claim}.
      - Using f_equal_nat we get `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y`{.claim} *by Corelib.Init.Peano.f_equal_nat*.
      - We deduce `S n0 = S (n0 + 0)`{.claim}.
- These cases being exhaustive, we deduce `n = n + 0`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
