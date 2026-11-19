---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# map_app

Let `A B : Type`{.var}. Let `f : A -> B`{.var}. Let `l : list A`{.var}. We prove `forall l' : list A, map f (l ++ l') = map f l ++ map f l'`{.claim}.

- We prove `forall l' : list A, map f (l ++ l') = map f l ++ map f l'` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - Case 1 (base): we prove `forall l' : list A, map f (nil ++ l') = map f nil ++ map f l'`{.claim}.
    - Let `l' : list A`{.var}. By definition of eq (*eq_refl*{.just}), we have `map f l' = map f l'`{.claim}.
  - Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall l' : list A, map f (l0 ++ l') = map f l0 ++ map f l') -> forall l' : list A, map f ((a :: l0) ++ l') = map f (a :: l0) ++ map f l'`{.claim}.
    - Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `forall l' : list A, map f (l0 ++ l') = map f l0 ++ map f l'`{.hyp} (IHl). Let `l' : list A`{.var}.
      - By definition of eq (*eq_refl*{.just}), we have `f a :: map f l0 ++ map f l' = f a :: map f l0 ++ map f l'`{.claim}.
      - Applying *IHl*{.just} to l', we have `map f (l0 ++ l') = map f l0 ++ map f l'`{.claim}.

      Rewriting with `map f (l0 ++ l') = map f l0 ++ map f l'`{.fact} from right to left (eq_ind_r), we get `f a :: map f (l0 ++ l') = f a :: map f l0 ++ map f l'`{.claim}.

  These cases being exhaustive, we deduce `forall l' : list A, map f (l ++ l') = map f l ++ map f l'`{.claim}.
