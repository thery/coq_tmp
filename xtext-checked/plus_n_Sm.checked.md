---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# plus_n_Sm'

✅ Let `n m : nat`{.var}. We prove `S (n + m) = n + S m`{.claim}.

- ▫️ We prove `S (n + m) = n + S m`{.fact} by induction on `n`{.fact} (nat, nat_ind):
- ✅ Case 1 (base): we prove `0 + S m = 0 + S m`{.claim}.
  - ✅ By definition of eq (eq_refl), we have `0 + S m = 0 + S m`{.claim} *by Corelib.Init.Logic.eq_refl*.
- ✅ Case 2 (inductive): we prove `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`{.claim}.
  - ▫️ Let us choose arbitrarily `n0 : nat`{.var}; assume by induction hypothesis `S (n0 + m) = n0 + S m`{.hyp} (IH).
    - ✅ By definition of eq (eq_refl), we have `S (n0 + S m) = S (n0 + S m)`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - ✅ By IH we have `S (n0 + m) = n0 + S m`{.claim}.
    - ✅ Rewriting with `S (n0 + m) = n0 + S m`{.fact} from right to left (eq_ind_r), we get `S (S (n0 + m)) = S (n0 + S m)`{.claim}.
- ✅ These cases being exhaustive, we deduce `S (n + m) = n + S m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
