---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# length_rev

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `length (rev l) = length l`{.claim}.

- We prove `length (rev l) = length l` by induction on `l` (list, *list_ind*{.just}):
  - Case 1 (base): we prove `length (rev (@nil A)) = length (@nil A)`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `0 = 0`{.claim}.
  - Case 2 (inductive): we prove `forall (a : A) (l0 : list A), length (rev l0) = length l0 -> length (rev (a :: l0)) = length (a :: l0)`{.claim}.
    - Let `a : A`{.var}. Let `l0 : list A`{.var}. Assume `length (rev l0) = length l0`{.hyp} (IHl).
      - Rewriting with `length (rev l0) = length l0`{.fact} from right to left (eq_ind_r), we get `length (rev l0) + length (a :: nil) = S (length l0)`{.claim}.
        - Rewriting with `length l0 + length (a :: nil) = length (a :: nil) + length l0`{.fact} from right to left (eq_ind_r), we get `length l0 + length (a :: nil) = S (length l0)`{.claim}.
          - By definition of eq (*eq_refl*{.just}), we have `S (length l0) = S (length l0)`{.claim}.
          - By application, we have `length l0 + length (a :: nil) = length (a :: nil) + length l0`{.claim}.
            - By application, we have `forall m : nat, length l0 + m = m + length l0`{.claim}.
              - By *PeanoNat.Nat.add_comm*{.just} we have `forall n m : nat, n + m = m + n`{.claim}.
              - The element `length l0` belongs to `nat`.
            - The element `length (a :: nil)` belongs to `nat`.
        - By *IHl*{.just} we have `length (rev l0) = length l0`{.claim}.
      - By application, we have `length (rev l0 ++ a :: nil) = length (rev l0) + length (a :: nil)`{.claim}.
        - By application, we have `forall l' : list A, length (rev l0 ++ l') = length (rev l0) + length l'`{.claim}.
          - By application, we have `forall l1 l' : list A, length (l1 ++ l') = length l1 + length l'`{.claim}.
            - By *List.length_app*{.just} we have `forall (A0 : Type) (l1 l' : list A0), length (l1 ++ l') = length l1 + length l'`{.claim}.
          - The element `rev l0` belongs to `list A`.
        - The element `a :: nil` belongs to `list A`.

      Rewriting with `length (rev l0 ++ a :: nil) = length (rev l0) + length (a :: nil)`{.fact} from right to left (eq_ind_r), we get `length (rev l0 ++ a :: nil) = S (length l0)`{.claim}.

  These cases being exhaustive, we deduce `length (rev l) = length l`{.claim}.
