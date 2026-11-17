<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive. -->

# le_n_S'

✅ Let `n m : nat`. Assume `n <= m` (H). We prove `S n <= S m`.

- ▫️ We prove `S n <= S m` by induction on `n <= m` (H) (le, le_ind):
- ✅ Case 1 (base): we prove `S n <= S n`.
  - ✅ By definition of le (le_n), we have `S n <= S n` .*by eapply @le_n; eauto*
- ✅ Case 2 (inductive): we prove `forall m0 : nat, n <= m0 -> S n <= S m0 -> S n <= S (S m0)`.
  - ▫️ Let us consider an arbitrary `m0 : nat`.
    - ▫️ Assume `n <= m0` (H0) and by induction hypothesis `S n <= S m0` (IH).
      - ✅ By definition of le (le_S) with witness `S m0`, from `S n <= S m0` (IH) we deduce `S n <= S (S m0)` .*by eapply @le_S; eauto*
- ✅ We have `S n <= S m` in all cases .*by eapply (@le_ind (n) (fun m0 : nat => S n <= S m0)); cbv beta; eauto*

