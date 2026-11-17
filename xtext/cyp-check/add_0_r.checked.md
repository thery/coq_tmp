<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.lemmas. -->

# add_0_r'

✅ Let `n : nat`. We prove `n + 0 = n`.

- ▫️ To prove `n + 0 = n` by induction (nat, nat_ind), we generalise it to `forall n0 : nat, n0 + 0 = n0`:
- ✅ Case 1 (base): we prove `0 = 0`.
  - ✅ By definition of eq (eq_refl), we have `0 = 0` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall m : nat, m + 0 = m -> S m + 0 = S m`.
  - ▫️ Let us consider an arbitrary `m : nat`.
    - ▫️ Assume by induction hypothesis `m + 0 = m` (IH).
      - ✅ By definition of eq (eq_refl), we have `S m = S m` .*by eapply @eq_refl; eauto*
      - ✅ By IH we have `m + 0 = m`.
      - ✅ Rewriting with `m + 0 = m` from right to left (eq_ind_r), we get `S (m + 0) = S m`.
- ✅ These cases being exhaustive, we deduce `forall n0 : nat, n0 + 0 = n0` .*by eapply (@nat_ind (fun n0 : nat => n0 + 0 = n0)); cbv beta; eauto*
- ✅ In particular `n + 0 = n`.

