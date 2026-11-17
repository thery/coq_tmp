<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List. Import ListNotations. Require Import XText.paper. -->

# le_0_m

✅ We prove `forall n : nat, 0 <= n`.

- ▫️ We prove `forall n : nat, 0 <= n` by induction (nat, nat_ind):
- ✅ Case 1 (base): we prove `0 <= 0`.
  - ✅ By definition of le (le_n), we have `0 <= 0` .*by eapply @le_n; eauto*
- ✅ Case 2 (inductive): we prove `forall m : nat, 0 <= m -> 0 <= S m`.
  - ▫️ Let us consider an arbitrary `m : nat`.
    - ▫️ Assume by induction hypothesis `0 <= m` (h).
      - ▫️ By definition of le (le_S) with witness `m`, from `0 <= m` (h) we deduce `0 <= S m` .*by eapply @le_S; eauto*
- ✅ These cases being exhaustive, we deduce `forall n : nat, 0 <= n`.

