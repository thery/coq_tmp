---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# length_app

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `forall l' : list A, length (l ++ l') = length l + length l'`{.claim}.

- We prove `forall l' : list A, length (l ++ l') = length l + length l'` by induction on `l` (list, *list_ind*{.just}):
  - Case 1 (base): we prove `forall l' : list A, @eq nat (@length A (@app A (@nil A) l')) (Init.Nat.add (@length A (@nil A)) (@length A l'))`{.claim}.
    - Let `l' : list A`{.var}. By definition of eq (*eq_refl*{.just}), we have `length l' = length l'`{.claim}.
  - Case 2 (inductive): we prove `forall (a : A) (l0 : list A), (forall l' : list A, length (l0 ++ l') = length l0 + length l') -> forall l' : list A, length ((a :: l0) ++ l') = length (a :: l0) + length l'`{.claim}.
    - Let `a : A`{.var}. Let `l0 : list A`{.var}. Assume `forall l' : list A, length (l0 ++ l') = length l0 + length l'`{.hyp} (IHl). Let `l' : list A`{.var}.
      - By application, we have `length (l0 ++ l') = length l0 + length l' -> S (length (l0 ++ l')) = S (length l0 + length l')`{.claim}.
        - By application, we have `forall y : nat, length (l0 ++ l') = y -> S (length (l0 ++ l')) = S y`{.claim}.
          - By application, we have `forall x y : nat, x = y -> S x = S y`{.claim}.
            - By application, we have `forall (f : nat -> nat) (x y : nat), x = y -> f x = f y`{.claim}.
              - By *f_equal_nat*{.just} we have `forall (B : Type) (f : nat -> B) (x y : nat), x = y -> f x = f y`{.claim}.
              - The element `nat` belongs to `Type`.
            - The element `S` belongs to `nat -> nat`.
          - The element `length (l0 ++ l')` belongs to `nat`.
        - The element `length l0 + length l'` belongs to `nat`.
      - By application, we have `length (l0 ++ l') = length l0 + length l'`{.claim}.
        - By *IHl*{.just} we have `forall l'0 : list A, length (l0 ++ l'0) = length l0 + length l'0`{.claim}.

      By application, we have `S (length (l0 ++ l')) = S (length l0 + length l')`{.claim}.

  These cases being exhaustive, we deduce `forall l' : list A, length (l ++ l') = length l + length l'`{.claim}.
