---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# map_map

Let `A B C : Type`{.var}. Let `f : A -> B`{.var}. Let `g : B -> C`{.var}. Let `l : list A`{.var}. We prove `map g (map f l) = map (fun x : A => g (f x)) l`{.claim}.

- To prove `map g (map f l) = map (fun x : A => g (f x)) l`{.fact} by induction (list, list_ind), we generalise it to `forall l0 : list A, map g (map f l0) = map (fun x : A => g (f x)) l0`{.fact}:
- Case 1 (base): we prove `map g (map f nil) = map (fun x : A => g (f x)) nil`{.claim}.
  - By definition of eq (eq_refl), we have `nil = (@nil C)`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), map g (map f l0) = map (fun x : A => g (f x)) l0 -> map g (map f (a :: l0)) = map (fun x : A => g (f x)) (a :: l0)`{.claim}.
  - Let `a : A`{.var}.
  - Let `l0 : list A`{.var}.
  - Assume by induction hypothesis `map g (map f l0) = map (fun x : A => g (f x)) l0`{.hyp} (IHl).
    - By definition of eq (eq_refl), we have `g (f a) :: map (fun x : A => g (f x)) l0 = g (f a) :: map (fun x : A => g (f x)) l0`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - By IHl we have `map g (map f l0) = map (fun x : A => g (f x)) l0`{.claim}.
    - Rewriting with `map g (map f l0) = map (fun x : A => g (f x)) l0`{.fact} from right to left (eq_ind_r), we get `g (f a) :: map g (map f l0) = g (f a) :: map (fun x : A => g (f x)) l0`{.claim}.
- These cases being exhaustive, we deduce `forall l0 : list A, map g (map f l0) = map (fun x : A => g (f x)) l0`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `map g (map f l) = map (fun x : A => g (f x)) l`{.claim}.
