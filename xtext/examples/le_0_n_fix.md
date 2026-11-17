---
require: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# le_0_n'

We prove `forall n : nat, 0 <= n`{.claim}.

- We prove `forall n : nat, 0 <= n`{.claim} by recursion on `n`{.fact} (fix le_0_n'):
  - Let us consider an arbitrary `n : nat`{.var}.
    - We prove `0 <= n`{.fact} by induction on `n`{.fact} (nat, match):
    - Case 1 (base): we prove `0 <= 0`{.claim}.
      - By definition of le (le_n), we have `0 <= 0`{.claim} *by eapply @le_n; eauto*.
    - Case 2 (inductive): we prove `forall m : nat, 0 <= S m`{.claim}.
      - Let us consider an arbitrary `m : nat`{.var}.
        - By induction hypothesis (the recursive call le_0_n') we have `forall n0 : nat, 0 <= n0`{.claim}.
        - In particular `0 <= m`{.claim}.
        - By definition of le (le_S) with witness `m`{.fact}, we have `0 <= S m`{.claim} *by eapply @le_S; eauto*.
    - These cases being exhaustive, we deduce `0 <= n`{.claim}.
