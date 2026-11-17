<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# map_app

✅ Let `A B : Type`. Let `f : A -> B`. Let `l : list A`. We prove `forall l' : list A, map f (l ++ l') = map f l ++ map f l'`.

- ▫️ To prove `forall l' : list A, map f (l ++ l') = map f l ++ map f l'` by induction (list, list_ind), we generalise it to `forall l0 l' : list A, map f (l0 ++ l') = map f l0 ++ map f l'`:
- ✅ Case 1 (base): we prove `forall l' : list A, map f (nil ++ l') = map f nil ++ map f l'`.
  - ▫️ Let `l' : list A`.
  - ✅ By definition of eq (eq_refl), we have `map f l' = map f l'` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall l' : list A, map f (l0 ++ l') = map f l0 ++ map f l') -> forall l' : list A, map f ((a :: l0) ++ l') = map f (a :: l0) ++ map f l'`.
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `forall l' : list A, map f (l0 ++ l') = map f l0 ++ map f l'` (IHl).
    - ▫️ Let `l' : list A`.
    - ✅ By definition of eq (eq_refl), we have `f a :: map f l0 ++ map f l' = f a :: map f l0 ++ map f l'` .*by eapply @eq_refl; eauto*
    - ✅ In particular `map f (l0 ++ l') = map f l0 ++ map f l'`.
      - ✅ By IHl we have `forall l'0 : list A, map f (l0 ++ l'0) = map f l0 ++ map f l'0`.
    - ✅ Rewriting with `map f (l0 ++ l') = map f l0 ++ map f l'` from right to left (eq_ind_r), we get `f a :: map f (l0 ++ l') = f a :: map f l0 ++ map f l'`.
- ✅ These cases being exhaustive, we deduce `forall l0 l' : list A, map f (l0 ++ l') = map f l0 ++ map f l'` .*by eapply (@list_ind (A) (fun l0 : list A => forall l' : list A, map f (l0 ++ l') = map f l0 ++ map f l')); cbv beta; eauto*
- ✅ In particular `forall l' : list A, map f (l ++ l') = map f l ++ map f l'`.

