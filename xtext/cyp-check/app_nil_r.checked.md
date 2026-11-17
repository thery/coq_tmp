<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive. -->

# app_nil_r'

✅ Let `A : Type`. Let `l : list A`. We prove `l ++ [] = l`.

- ▫️ To prove `l ++ [] = l` by induction (list, list_ind), we generalise it to `forall l0 : list A, l0 ++ [] = l0`:
- ✅ Case 1 (base): we prove `([]) = ([]) :> list A`.
  - ✅ By definition of eq (eq_refl), we have `([]) = ([]) :> list A` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall (x : A) (l0 : list A), l0 ++ [] = l0 -> (x :: l0) ++ [] = x :: l0`.
  - ▫️ Let `x : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `l0 ++ [] = l0` (IH).
    - ✅ By definition of eq (eq_refl), we have `x :: l0 = x :: l0` .*by eapply @eq_refl; eauto*
    - ✅ By IH we have `l0 ++ [] = l0`.
    - ✅ Rewriting with `l0 ++ [] = l0` from right to left (eq_ind_r), we get `x :: l0 ++ [] = x :: l0`.
- ✅ These cases being exhaustive, we deduce `forall l0 : list A, l0 ++ [] = l0` .*by eapply (@list_ind (A) (fun l0 : list A => l0 ++ [] = l0)); cbv beta; eauto*
- ✅ In particular `l ++ [] = l`.

