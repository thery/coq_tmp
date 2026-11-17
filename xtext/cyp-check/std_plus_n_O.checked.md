<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# plus_n_O

✅ Let `n : nat`. We prove `n = n + 0`.

- ▫️ To prove `n = n + 0` by induction (nat, nat_ind), we generalise it to `forall n0 : nat, n0 = n0 + 0`:
- ✅ Case 1 (base): we prove `0 = 0 + 0`.
  - ✅ By definition of eq (eq_refl), we have `0 = 0` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall n0 : nat, n0 = n0 + 0 -> S n0 = S n0 + 0`.
  - ▫️ Let us consider an arbitrary `n0 : nat`.
    - ▫️ Assume by induction hypothesis `n0 = n0 + 0` (IHn).
      - ✅ By IHn we have `n0 = n0 + 0`.
      - ✅ In particular `n0 = n0 + 0 -> S n0 = S (n0 + 0)`.
        - ✅ Using f_equal_nat we get `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y` .*by exact @f_equal_nat*
      - ✅ We deduce `S n0 = S (n0 + 0)`.
- ✅ These cases being exhaustive, we deduce `forall n0 : nat, n0 = n0 + 0` .*by eapply (@nat_ind (fun n0 : nat => n0 = n0 + 0)); cbv beta; eauto*
- ✅ In particular `n = n + 0`.

