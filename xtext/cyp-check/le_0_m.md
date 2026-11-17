---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# le_0_m

We prove `forall n : nat, 0 <= n`{.claim}.

- We prove `forall n : nat, 0 <= n`{.fact} by induction (nat, nat_ind):
- Case 1 (base): we prove `0 <= 0`{.claim}.
  - By definition of le (le_n), we have `0 <= 0`{.claim} *by eapply @le_n; eauto*.
- Case 2 (inductive): we prove `forall m : nat, 0 <= m -> 0 <= S m`{.claim}.
  - Let us consider an arbitrary `m : nat`{.var}.
    - Assume by induction hypothesis `0 <= m`{.hyp} (h).
      - By definition of le (le_S) with witness `m`{.fact}, from `0 <= m`{.fact} (h) we deduce `0 <= S m`{.claim} *by eapply @le_S; eauto*.
- These cases being exhaustive, we deduce `forall n : nat, 0 <= n`{.claim} *by eapply (@nat_ind (fun x : nat => 0 <= x)); cbv beta; eauto*.
