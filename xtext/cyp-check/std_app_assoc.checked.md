<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# app_assoc

✅ Let `A : Type`. Let `l m n : list A`. We prove `l ++ m ++ n = (l ++ m) ++ n`.

- ▫️ To prove `l ++ m ++ n = (l ++ m) ++ n` by induction (list, list_ind), we generalise it to `forall l0 : list A, l0 ++ m ++ n = (l0 ++ m) ++ n`:
- ✅ Case 1 (base): we prove `nil ++ m ++ n = (nil ++ m) ++ n`.
  - ✅ By definition of eq (eq_refl), we have `n = n`  (H).*by eapply @eq_refl; eauto*
  - ✅ By H we have `n = n`.
  - ✅ We deduce `n = n -> m ++ n = m ++ n`.
    - ✅ By definition of eq (eq_refl), we have `m = m`  (H0).*by eapply @eq_refl; eauto*
    - ✅ By H0 we have `m = m`.
    - ✅ We have proved `m = m -> n = n -> m ++ n = m ++ n`.
      - ✅ By definition of eq (eq_refl), we have `A = A`  (H1).*by eapply @eq_refl; eauto*
      - ▫️ Assume `m = m` (H00) and `n = n` (H10).
        - ✅ By definition of eq (eq_refl), we have `m ++ n = m ++ n` .*by eapply @eq_refl; eauto*
  - ✅ We deduce `m ++ n = m ++ n`.
- ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ m ++ n = (l0 ++ m) ++ n -> (a :: l0) ++ m ++ n = ((a :: l0) ++ m) ++ n`.
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `l0 ++ m ++ n = (l0 ++ m) ++ n` (IHl).
    - ✅ By IHl we have `l0 ++ m ++ n = (l0 ++ m) ++ n` (H).
    - ✅ By H we have `l0 ++ m ++ n = (l0 ++ m) ++ n`.
    - ✅ We deduce `l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`.
      - ✅ By definition of eq (eq_refl), we have `a = a`  (H0).*by eapply @eq_refl; eauto*
      - ✅ By H0 we have `a = a`.
      - ✅ We have proved `a = a -> l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`.
        - ✅ By definition of eq (eq_refl), we have `A = A`  (H1).*by eapply @eq_refl; eauto*
        - ▫️ Assume `a = a` (H00) and `l0 ++ m ++ n = (l0 ++ m) ++ n` (H10).
          - ✅ We deduce `a :: l0 ++ m ++ n = a :: l0 ++ m ++ n` , that is `a :: l0 ++ m ++ n = a :: l0 ++ m ++ n`.*by tauto*
            - ✅ By definition of eq (eq_refl), we have `cons a = cons a` .*by eapply @eq_refl; eauto*
            - ✅ Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y` .*by exact @Corelib.Init.Logic.f_equal*
          - ✅ We deduce `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`, that is `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`.
            - ✅ By H10 we have `l0 ++ m ++ n = (l0 ++ m) ++ n`.
            - ✅ Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y` .*by exact @Corelib.Init.Logic.f_equal*
          - ✅ Using eq_trans we get `forall (A0 : Type) (x y z : A0), x = y -> y = z -> x = z` .*by exact @Corelib.Init.Logic.eq_trans*
          - ✅ We deduce `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`.
    - ✅ We deduce `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`.
- ✅ These cases being exhaustive, we deduce `forall l0 : list A, l0 ++ m ++ n = (l0 ++ m) ++ n` .*by eapply (@list_ind (A) (fun l0 : list A => l0 ++ m ++ n = (l0 ++ m) ++ n)); cbv beta; eauto*
- ✅ In particular `l ++ m ++ n = (l ++ m) ++ n`.

