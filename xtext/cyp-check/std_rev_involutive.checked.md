<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# rev_involutive

✅ Let `A : Type`. Let `l : list A`. We prove `rev (rev l) = l`.

- ▫️ To prove `rev (rev l) = l` by induction (list, list_ind), we generalise it to `forall l0 : list A, rev (rev l0) = l0`:
- ✅ Case 1 (base): we prove `nil = (@nil A)`.
  - ✅ By definition of eq (eq_refl), we have `nil = (@nil A)` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), rev (rev l0) = l0 -> rev (rev (a :: l0)) = a :: l0`.
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `rev (rev l0) = l0` (IHl).
    - ✅ Rewriting with `rev (rev l0) = l0` from right to left (eq_ind_r), we get `a :: rev (rev l0) = a :: l0`.
      - ✅ By definition of eq (eq_refl), we have `a :: l0 = a :: l0` .*by eapply @eq_refl; eauto*
      - ✅ By IHl we have `rev (rev l0) = l0`.
    - ✅ In particular `rev (rev l0 ++ a :: nil) = a :: rev (rev l0)`.
      - ✅ Using rev_unit we get `forall (A0 : Type) (l1 : list A0) (a0 : A0), rev (l1 ++ a0 :: nil) = a0 :: rev l1` .*by exact @Stdlib.Lists.List.rev_unit*
    - ✅ Rewriting with `rev (rev l0 ++ a :: nil) = a :: rev (rev l0)` from right to left (eq_ind_r), we get `rev (rev l0 ++ a :: nil) = a :: l0`.
- ✅ These cases being exhaustive, we deduce `forall l0 : list A, rev (rev l0) = l0` .*by eapply (@list_ind (A) (fun l0 : list A => rev (rev l0) = l0)); cbv beta; eauto*
- ✅ In particular `rev (rev l) = l`.

