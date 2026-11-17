<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas. -->

# le_add_r'

✅ Let `n m : nat`. We prove `n <= n + m`.

- ▫️ To prove `n <= n + m` by induction (nat, nat_ind), we generalise it to `forall n0 : nat, n <= n + n0`:
- ✅ Case 1 (base): we prove `n <= n + 0`.
  - ✅ By definition of le (le_n), we have `n <= n` .*by eapply @le_n; eauto*
  - ✅ In particular `n + 0 = n`.
    - ✅ Using add_0_r we get `forall n0 : nat, n0 + 0 = n0` .*by exact @Stdlib.Arith.PeanoNat.Nat.add_0_r*
  - ✅ Rewriting with `n + 0 = n` from right to left (eq_ind_r), we get `n <= n + 0`.
- ✅ Case 2 (inductive): we prove `forall m0 : nat, n <= n + m0 -> n <= n + S m0`.
  - ▫️ Let us consider an arbitrary `m0 : nat`.
    - ▫️ Assume by induction hypothesis `n <= n + m0` (IH).
      - ✅ By definition of le (le_S) with witness `n + m0`, from `n <= n + m0` (IH) we deduce `n <= S (n + m0)` .*by eapply @le_S; eauto*
      - ✅ In particular `n + S m0 = S (n + m0)`.
        - ✅ Using add_succ_r we get `forall n0 m1 : nat, n0 + S m1 = S (n0 + m1)` .*by exact @Stdlib.Arith.PeanoNat.Nat.add_succ_r*
      - ✅ Rewriting with `n + S m0 = S (n + m0)` from right to left (eq_ind_r), we get `n <= n + S m0`.
- ✅ These cases being exhaustive, we deduce `forall n0 : nat, n <= n + n0` .*by eapply (@nat_ind (fun m0 : nat => n <= n + m0)); cbv beta; eauto*
- ✅ In particular `n <= n + m`.

