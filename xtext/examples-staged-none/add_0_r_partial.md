---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial.
by: tauto | congruence | lia | firstorder | auto
---

# add_0_r_partial (proof in progress)

Let `n : nat`{.var}. We prove `n + 0 = n`{.claim}.

- We prove `n + 0 = n`{.fact} by induction on `n`{.fact} (nat, nat_ind):
- Case 1 (base): we prove `0 = 0`{.claim}.
  - By definition of eq (eq_refl), we have `0 = 0`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall m : nat, m + 0 = m -> S m + 0 = S m`{.claim}.
  - Let us choose arbitrarily `m : nat`{.var}.
    - Assume `m + 0 = m`{.hyp} (IH).
      - Prove `S m + 0 = S m`{.claim}.
- These cases being exhaustive, we deduce `n + 0 = n`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
