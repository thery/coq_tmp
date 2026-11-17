<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# rev_app_distr

✅ Let `A : Type`. Let `x y : list A`. We prove `rev (x ++ y) = rev y ++ rev x`.

- ▫️ To prove `rev (x ++ y) = rev y ++ rev x` by induction (list, list_ind), we generalise it to `forall l : list A, rev (l ++ y) = rev y ++ rev l`:
- ✅ Case 1 (base): we prove `rev (nil ++ y) = rev y ++ rev nil`.
  - ✅ By definition of eq (eq_refl), we have `rev y = rev y` .*by eapply @eq_refl; eauto*
  - ✅ In particular `rev y ++ nil = rev y`.
    - ✅ Using app_nil_r we get `forall (A0 : Type) (l : list A0), l ++ nil = l` .*by exact @Stdlib.Lists.List.app_nil_r*
  - ✅ Rewriting with `rev y ++ nil = rev y` from right to left (eq_ind_r), we get `rev y = rev y ++ nil`.
- ✅ Case 2 (inductive): we prove `forall (a : A) (l : list A), rev (l ++ y) = rev y ++ rev l -> rev ((a :: l) ++ y) = rev y ++ rev (a :: l)`.
  - ▫️ Let `a : A`.
  - ▫️ Let `l : list A`.
  - ▫️ Assume by induction hypothesis `rev (l ++ y) = rev y ++ rev l` (IHl).
    - ✅ Rewriting with `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil` from right to left (eq_ind_r), we get `(rev y ++ rev l) ++ a :: nil = rev y ++ rev l ++ a :: nil`.
      - ✅ By definition of eq (eq_refl), we have `(rev y ++ rev l) ++ a :: nil = (rev y ++ rev l) ++ a :: nil` .*by eapply @eq_refl; eauto*
      - ✅ In particular `rev y ++ rev l ++ a :: nil = (rev y ++ rev l) ++ a :: nil`.
        - ✅ Using app_assoc we get `forall (A0 : Type) (l0 m n : list A0), l0 ++ m ++ n = (l0 ++ m) ++ n` .*by exact @Stdlib.Lists.List.app_assoc*
    - ✅ By IHl we have `rev (l ++ y) = rev y ++ rev l`.
    - ✅ Rewriting with `rev (l ++ y) = rev y ++ rev l` from right to left (eq_ind_r), we get `rev (l ++ y) ++ a :: nil = rev y ++ rev l ++ a :: nil`.
- ✅ These cases being exhaustive, we deduce `forall l : list A, rev (l ++ y) = rev y ++ rev l` .*by eapply (@list_ind (A) (fun x0 : list A => rev (x0 ++ y) = rev y ++ rev x0)); cbv beta; eauto*
- ✅ In particular `rev (x ++ y) = rev y ++ rev x`.

