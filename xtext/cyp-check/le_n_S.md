---
require: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# le_n_S'

Let `n m : nat`{.var}. Assume `n <= m`{.hyp} (H). We prove `S n <= S m`{.claim}.

- We prove `S n <= S m`{.fact} by induction on `n <= m`{.fact} (H) (le, le_ind):
- Case 1 (base): we prove `S n <= S n`{.claim}.
  - By definition of le (le_n), we have `S n <= S n`{.claim} *by eapply @le_n; eauto*.
- Case 2 (inductive): we prove `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`{.claim}.
  - Let us consider an arbitrary `m0 : nat`{.var}.
    - Assume `n <= m0`{.hyp} (H0) and by induction hypothesis `S n <= S m0`{.hyp} (IH).
      - By definition of le (le_S) with witness `S m0`{.fact}, from `S n <= S m0`{.fact} (IH) we deduce `S n <= S (S m0)`{.claim} *by eapply @le_S; eauto*.
- We have `S n <= S m`{.claim} in all cases.
