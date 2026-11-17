<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive. -->

# le_0_n'

✅ We prove `forall n : nat, 0 <= n`.

- ✅ We prove `forall n : nat, 0 <= n` by recursion on `n` (fix le_0_n'):
  - ▫️ Let us consider an arbitrary `n : nat`.
    - ▫️ We prove `0 <= n` by induction on `n` (nat, match):
    - ✅ Case 1 (base): we prove `0 <= 0`.
      - ✅ By definition of le (le_n), we have `0 <= 0` .*by eapply @le_n; eauto*
    - ✅ Case 2 (inductive): we prove `forall m : nat, 0 <= S m`.
      - ▫️ Let us consider an arbitrary `m : nat`.
        - ✅ By induction hypothesis (the recursive call le_0_n') we have `forall n0 : nat, 0 <= n0`.
        - ✅ In particular `0 <= m`.
        - ✅ By definition of le (le_S) with witness `m`, we have `0 <= S m` .*by eapply @le_S; eauto*
    - ✅ These cases being exhaustive, we deduce `0 <= n` .*by destruct n; cbn; eauto*

