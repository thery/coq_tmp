---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas.
by: tauto | congruence | lia | firstorder | auto
---

# le_add_r'

Let `n m : nat`{.var}. We prove `n <= n + m`{.claim}.

- We prove `n <= n + m`{.fact} by induction on `m`{.fact} (nat, nat_ind):
- Case 1 (base): we prove `n <= n + 0`{.claim}.
  - By definition of le (le_n), we have `n <= n`{.claim} *by Corelib.Init.Peano.le_n*.
  - Applying add_0_r to n, we have `n + 0 = n`{.claim}.
  - Rewriting with `n + 0 = n`{.fact} from right to left (eq_ind_r), we get `n <= n + 0`{.claim}.
- Case 2 (inductive): we prove `forall m0 : nat, n <= n + m0 -> n <= n + S m0`{.claim}.
  - Let us choose arbitrarily `m0 : nat`{.var}; assume by induction hypothesis `n <= n + m0`{.hyp} (IH).
    - By definition of le (le_S) with witness `n + m0`{.fact}, from `n <= n + m0`{.fact} (IH) we deduce `n <= S (n + m0)`{.claim} *by Corelib.Init.Peano.le_S*.
    - Applying add_succ_r to n and m0, we have `n + S m0 = S (n + m0)`{.claim}.
    - Rewriting with `n + S m0 = S (n + m0)`{.fact} from right to left (eq_ind_r), we get `n <= n + S m0`{.claim}.
- These cases being exhaustive, we deduce `n <= n + m`{.claim} *by Corelib.Init.Datatypes.nat_ind*.
