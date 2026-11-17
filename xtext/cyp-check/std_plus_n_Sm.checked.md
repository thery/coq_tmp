<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# plus_n_Sm

✅ Let `n m : nat`. We prove `S (n + m) = n + S m`.

- ▫️ To prove `S (n + m) = n + S m` by induction (nat, nat_ind), we generalise it to `forall n0 : nat, S (n0 + m) = n0 + S m`:
- ✅ Case 1 (base): we prove `S (0 + m) = 0 + S m`.
  - ✅ By definition of eq (eq_refl), we have `S m = S m` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall n0 : nat, S (n0 + m) = n0 + S m -> S (S n0 + m) = S n0 + S m`.
  - ▫️ Let us consider an arbitrary `n0 : nat`.
    - ▫️ Assume by induction hypothesis `S (n0 + m) = n0 + S m` (IHn).
      - ✅ By IHn we have `S (n0 + m) = n0 + S m`.
      - ✅ Using f_equal_nat we get `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y` .*by exact @Corelib.Init.Peano.f_equal_nat*
      - ✅ We deduce `S (S (n0 + m)) = S (n0 + S m)`.
- ✅ These cases being exhaustive, we deduce `forall n0 : nat, S (n0 + m) = n0 + S m` .*by eapply (@nat_ind (fun n0 : nat => S (n0 + m) = n0 + S m)); cbv beta; eauto*
- ✅ In particular `S (n + m) = n + S m`.

