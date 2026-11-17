<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# length_app

✅ Let `A : Type`. Let `l : list A`. We prove `forall l' : list A, length (l ++ l') = length l + length l'`.

- ▫️ To prove `forall l' : list A, length (l ++ l') = length l + length l'` by induction (list, list_ind), we generalise it to `forall l0 l' : list A, length (l0 ++ l') = length l0 + length l'`:
- ✅ Case 1 (base): we prove `forall l' : list A, @eq nat (@length A (@app A (@nil A) l')) (Init.Nat.add (@length A (@nil A)) (@length A l'))`.
  - ▫️ Let `l' : list A`.
  - ✅ By definition of eq (eq_refl), we have `length l' = length l'` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall l' : list A, length (l0 ++ l') = length l0 + length l') -> forall l' : list A, length ((a :: l0) ++ l') = length (a :: l0) + length l'`.
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `forall l' : list A, length (l0 ++ l') = length l0 + length l'` (IHl).
    - ▫️ Let `l' : list A`.
    - ✅ In particular `length (l0 ++ l') = length l0 + length l'`.
      - ✅ By IHl we have `forall l'0 : list A, length (l0 ++ l'0) = length l0 + length l'0`.
    - ✅ Using f_equal_nat we get `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y` .*by exact @Corelib.Init.Peano.f_equal_nat*
    - ✅ We deduce `S (length (l0 ++ l')) = S (length l0 + length l')`.
- ✅ These cases being exhaustive, we deduce `forall l0 l' : list A, length (l0 ++ l') = length l0 + length l'` .*by eapply (@list_ind (A) (fun l0 : list A => forall l' : list A, length (l0 ++ l') = length l0 + length l')); cbv beta; eauto*
- ✅ In particular `forall l' : list A, length (l ++ l') = length l + length l'`.

