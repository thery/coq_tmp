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
    - Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `n0 = n0 + 0`{.hyp} (IHn).
      - The element `n0 + 0` belongs to `nat`.

      Applying *f_equal_nat*{.just} to nat, S, n0 and *IHn*{.just}, we have `S n0 = S (n0 + 0)`{.claim}.

  These cases being exhaustive, we deduce `n = n + 0`{.claim}.
