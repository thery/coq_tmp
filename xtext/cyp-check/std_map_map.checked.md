<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# map_map

✅ Let `A B C : Type`. Let `f : A -> B`. Let `g : B -> C`. Let `l : list A`. We prove `map g (map f l) = map (fun x : A => g (f x)) l`.

- ▫️ To prove `map g (map f l) = map (fun x : A => g (f x)) l` by induction (list, list_ind), we generalise it to `forall l0 : list A, map g (map f l0) = map (fun x : A => g (f x)) l0`:
- ✅ Case 1 (base): we prove `map g (map f nil) = map (fun x : A => g (f x)) nil`.
  - ✅ By definition of eq (eq_refl), we have `nil = (@nil C)` .*by eapply @eq_refl; eauto*
- ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), map g (map f l0) = map (fun x : A => g (f x)) l0 -> map g (map f (a :: l0)) = map (fun x : A => g (f x)) (a :: l0)`.
  - ▫️ Let `a : A`.
  - ▫️ Let `l0 : list A`.
  - ▫️ Assume by induction hypothesis `map g (map f l0) = map (fun x : A => g (f x)) l0` (IHl).
    - ✅ By definition of eq (eq_refl), we have `g (f a) :: map (fun x : A => g (f x)) l0 = g (f a) :: map (fun x : A => g (f x)) l0` .*by eapply @eq_refl; eauto*
    - ✅ By IHl we have `map g (map f l0) = map (fun x : A => g (f x)) l0`.
    - ✅ Rewriting with `map g (map f l0) = map (fun x : A => g (f x)) l0` from right to left (eq_ind_r), we get `g (f a) :: map g (map f l0) = g (f a) :: map (fun x : A => g (f x)) l0`.
- ✅ These cases being exhaustive, we deduce `forall l0 : list A, map g (map f l0) = map (fun x : A => g (f x)) l0` .*by eapply (@list_ind (A) (fun l0 : list A => map g (map f l0) = map (fun x : A => g (f x)) l0)); cbv beta; eauto*
- ✅ In particular `map g (map f l) = map (fun x : A => g (f x)) l`.

