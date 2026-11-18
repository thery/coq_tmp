---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# map_app

Let `A B : Type`{.var}. Let `f : A -> B`{.var}. Let `l : list A`{.var}. We prove `forall l' : list A, map f (l ++ l') = map f l ++ map f l'`{.claim}.

- To prove `forall l' : list A, map f (l ++ l') = map f l ++ map f l'`{.fact} by induction (list, list_ind), we generalise it to `forall l0 l' : list A, map f (l0 ++ l') = map f l0 ++ map f l'`{.fact}:
- Case 1 (base): we prove `forall l' : list A, map f (nil ++ l') = map f nil ++ map f l'`{.claim}.
  - Let `l' : list A`{.var}.
  - By definition of eq (eq_refl), we have `map f l' = map f l'`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall l' : list A, map f (l0 ++ l') = map f l0 ++ map f l') -> forall l' : list A, map f ((a :: l0) ++ l') = map f (a :: l0) ++ map f l'`{.claim}.
  - Let `a : A`{.var}.
  - Let `l0 : list A`{.var}.
  - Assume by induction hypothesis `forall l' : list A, map f (l0 ++ l') = map f l0 ++ map f l'`{.hyp} (IHl).
    - Let `l' : list A`{.var}.
    - By definition of eq (eq_refl), we have `f a :: map f l0 ++ map f l' = f a :: map f l0 ++ map f l'`{.claim} *by Corelib.Init.Logic.eq_refl*.
    - In particular `map f (l0 ++ l') = map f l0 ++ map f l'`{.claim}.
      - By IHl we have `forall l'0 : list A, map f (l0 ++ l'0) = map f l0 ++ map f l'0`{.claim}.
    - Rewriting with `map f (l0 ++ l') = map f l0 ++ map f l'`{.fact} from right to left (eq_ind_r), we get `f a :: map f (l0 ++ l') = f a :: map f l0 ++ map f l'`{.claim}.
- These cases being exhaustive, we deduce `forall l0 l' : list A, map f (l0 ++ l') = map f l0 ++ map f l'`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `forall l' : list A, map f (l ++ l') = map f l ++ map f l'`{.claim}.
