---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm

Let `n m : nat`{.var}. We prove `S (n + m) = n + S m`{.claim}.

- We prove `S (n + m) = n + S m` by induction on `n` (nat, *nat_ind*{.just}):
  - Case 1 (base): we prove `S (0 + m) = 0 + S m`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `S m = S m`{.claim}.
  - Case 2 (inductive): we prove `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
    - Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `S (n0 + m) = n0 + S m`{.hyp} (IHn).
      - The element `S (n0 + m)` belongs to `nat`.
      - The element `n0 + S m` belongs to `nat`.

      Applying *f_equal_nat*{.just} to nat, S and *IHn*{.just}, we have `S (S (n0 + m)) = S (n0 + S m)`{.claim}.

  These cases being exhaustive, we deduce `S (n + m) = n + S m`{.claim}.
