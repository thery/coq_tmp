<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# app_nil_r

✅ Let `A : Type`. Let `l : list A`. We prove `l ++ nil = l`.

- ▫️ To prove `l ++ nil = l` by induction (list, list_ind), we generalise it to `forall l0 : list A, l0 ++ nil = l0`:
- ✅ Case 1 (base): we prove `(nil ++ nil) = (nil) :> list A`.
  - ✅ By definition of eq (eq_refl), we have `A = A`  (H).*by eapply @eq_refl; eauto*
  - ✅ By definition of eq (eq_refl), we have `(nil) = (nil) :> list A` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ nil = l0 -> (a :: l0) ++ nil = a :: l0`.
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `l0 ++ nil = l0` (IHl).
    - ✅ By IHl we have `l0 ++ nil = l0` (H).
    - ✅ By H we have `l0 ++ nil = l0`.
    - ✅ We deduce `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`.
      - ✅ By definition of eq (eq_refl), we have `a = a`  (H0).*by eapply @eq_refl; eauto*
      - ✅ By H0 we have `a = a`.
      - ✅ We have proved `a = a -> l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`.
        - ✅ By definition of eq (eq_refl), we have `A = A`  (H1).*by eapply @eq_refl; eauto*
        - ▫️ Assume `a = a` (H00) and `l0 ++ nil = l0` (H10).
          - ✅ We deduce `a :: l0 ++ nil = a :: l0 ++ nil`.
            - ✅ By definition of eq (eq_refl), we have `cons a = cons a` .*by eapply @eq_refl; eauto*
            - ✅ In particular `cons a = cons a -> a :: l0 ++ nil = a :: l0 ++ nil`.
              - ✅ Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y` .*by exact @f_equal*
          - ✅ We deduce `a :: l0 ++ nil = a :: l0`.
            - ✅ By H10 we have `l0 ++ nil = l0`.
            - ✅ In particular `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`.
              - ✅ Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y` .*by exact @f_equal*
          - ✅ In particular `a :: l0 ++ nil = a :: l0 ++ nil -> a :: l0 ++ nil = a :: l0 -> a :: l0 ++ nil = a :: l0`.
            - ✅ Using eq_trans we get `forall (A0 : Type) (x y z : A0), x = y -> y = z -> x = z` .*by exact @eq_trans*
          - ✅ We deduce `a :: l0 ++ nil = a :: l0`.
    - ✅ We deduce `a :: l0 ++ nil = a :: l0`.
- ✅ These cases being exhaustive, we deduce `forall l0 : list A, l0 ++ nil = l0` .*by eapply (@list_ind (A) (fun l0 : list A => l0 ++ nil = l0)); cbv beta; eauto*
- ✅ In particular `l ++ nil = l`.

