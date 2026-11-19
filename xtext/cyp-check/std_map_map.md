---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# map_map

Let `A B C : Type`{.var}. Let `f : A -> B`{.var}. Let `g : B -> C`{.var}. Let `l : list A`{.var}. We prove `map g (map f l) = map (fun x : A => g (f x)) l`{.claim}.

- We prove `map g (map f l) = map (fun x : A => g (f x)) l` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - Case 1 (base): we prove `map g (map f nil) = map (fun x : A => g (f x)) nil`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `nil = (@nil C)`{.claim}.
  - Case 2 (inductive): we prove `forall (a : A) (l0 : list A), map g (map f l0) = map (fun x : A => g (f x)) l0 -> map g (map f (a :: l0)) = map (fun x : A => g (f x)) (a :: l0)`{.claim}.
    - Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `map g (map f l0) = map (fun x : A => g (f x)) l0`{.hyp} (IHl).
      - By definition of eq (*eq_refl*{.just}), we have `g (f a) :: map (fun x : A => g (f x)) l0 = g (f a) :: map (fun x : A => g (f x)) l0`{.claim}.
      - By *IHl*{.just} we have `map g (map f l0) = map (fun x : A => g (f x)) l0`{.claim}.

      Rewriting with `map g (map f l0) = map (fun x : A => g (f x)) l0`{.fact} from right to left (eq_ind_r), we get `g (f a) :: map g (map f l0) = g (f a) :: map (fun x : A => g (f x)) l0`{.claim}.

  These cases being exhaustive, we deduce `map g (map f l) = map (fun x : A => g (f x)) l`{.claim}.
