---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# length_app

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `forall l' : list A, length (l ++ l') = length l + length l'`{.claim}.

- We prove `forall l' : list A, length (l ++ l') = length l + length l'` by induction on `l` (list, *list_ind*{.just}):
  - Case 1 (base): we prove `forall l' : list A, @eq nat (@length A (@app A (@nil A) l')) (Init.Nat.add (@length A (@nil A)) (@length A l'))`{.claim}.
    - Let `l' : list A`{.var}. By definition of eq (*eq_refl*{.just}), we have `length l' = length l'`{.claim}.
  - Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall l' : list A, length (l0 ++ l') = length l0 + length l') -> forall l' : list A, length ((a :: l0) ++ l') = length (a :: l0) + length l'`{.claim}.
    - Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `forall l' : list A, length (l0 ++ l') = length l0 + length l'`{.hyp} (IHl). Let `l' : list A`{.var}.
      - The element `nat` belongs to `Type`.
      - The element `S` belongs to `nat -> nat`.
      - The element `length (l0 ++ l')` belongs to `nat`.
      - The element `length l0 + length l'` belongs to `nat`.
      - Applying *IHl*{.just} to l', we have `length (l0 ++ l') = length l0 + length l'`{.claim}.

      Applying *f_equal_nat*{.just}, we have `S (length (l0 ++ l')) = S (length l0 + length l')`{.claim}.

  These cases being exhaustive, we deduce `forall l' : list A, length (l ++ l') = length l + length l'`{.claim}.
