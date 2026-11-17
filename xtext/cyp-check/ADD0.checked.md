<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# ADD0

✅ Let `m : nat`. We prove `m + 0 = m`.

- ▫️ To prove `m + 0 = m` by induction (nat, nat_ind), we generalise it to `forall n : nat, n + 0 = n`:
- ✅ Case 1 (base): we prove `0 + 0 = 0 + 0`.
  - ✅ By definition of eq (eq_refl), we have `0 + 0 = 0 + 0` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall m0 : nat, m0 + 0 = m0 -> S (m0 + 0) = S m0`.
  - ▫️ Let us consider an arbitrary `m0 : nat`.
    - ▫️ Assume by induction hypothesis `m0 + 0 = m0` (IH).
      - ✅ By IH we have `m0 + 0 = m0`.
      - ✅ Using f_equal we get `forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y` .*by exact @Corelib.Init.Logic.f_equal*
      - ✅ We deduce `S (m0 + 0) = S m0`.
- ✅ These cases being exhaustive, we deduce `forall n : nat, n + 0 = n` .*by eapply (@nat_ind (fun m0 : nat => m0 + 0 = m0)); cbv beta; eauto*
- ✅ In particular `m + 0 = m`.

