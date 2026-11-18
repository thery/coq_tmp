---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# length_app

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `forall l' : list A, length (l ++ l') = length l + length l'`{.claim}.

- To prove `forall l' : list A, length (l ++ l') = length l + length l'`{.fact} by induction (list, list_ind), we generalise it to `forall l0 l' : list A, length (l0 ++ l') = length l0 + length l'`{.fact}:
- Case 1 (base): we prove `forall l' : list A, @eq nat (@length A (@app A (@nil A) l')) (Init.Nat.add (@length A (@nil A)) (@length A l'))`{.claim}.
  - Let `l' : list A`{.var}.
    - By definition of eq (eq_refl), we have `length l' = length l'`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall l' : list A, length (l0 ++ l') = length l0 + length l') -> forall l' : list A, length ((a :: l0) ++ l') = length (a :: l0) + length l'`{.claim}.
  - Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `forall l' : list A, length (l0 ++ l') = length l0 + length l'`{.hyp} (IHl).
    - Let `l' : list A`{.var}.
      - Applying IHl to l', we have `length (l0 ++ l') = length l0 + length l'`{.claim} (P1).
      - The element `length (l0 ++ l')`{.fact} belongs to `nat`{.fact}.
      - The element `length l0 + length l'`{.fact} belongs to `nat`{.fact}.
      - Applying f_equal_nat to nat, S and P1, we have `S (length (l0 ++ l')) = S (length l0 + length l')`{.claim}.
- These cases being exhaustive, we deduce `forall l0 l' : list A, length (l0 ++ l') = length l0 + length l'`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `forall l' : list A, length (l ++ l') = length l + length l'`{.claim}.
