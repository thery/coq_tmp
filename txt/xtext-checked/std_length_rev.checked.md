---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# length_rev

✅ Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `length (rev l) = length l`{.claim}.

- ✅ We prove `length (rev l) = length l` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - ✅ Case 1 (base): we prove `length (rev (@nil A)) = length (@nil A)`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `0 = 0`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), length (rev l0) = length l0 -> length (rev (a :: l0)) = length (a :: l0)`{.claim}.
    - ✅ Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `length (rev l0) = length l0`{.hyp} (IHl).
      - ✅ Rewriting with `length (rev l0) = length l0`{.fact} from right to left (eq_ind_r), we get `length (rev l0) + length (a :: nil) = S (length l0)`{.claim}.
        - ✅ Rewriting with `length l0 + length (a :: nil) = length (a :: nil) + length l0`{.fact} from right to left (eq_ind_r), we get `length l0 + length (a :: nil) = S (length l0)`{.claim}.
          - ✅ By definition of eq (*eq_refl*{.just}), we have `S (length l0) = S (length l0)`{.claim}.
          - ✅ Applying *PeanoNat.Nat.add_comm*{.just}, we have `length l0 + length (a :: nil) = length (a :: nil) + length l0`{.claim}.
            - ▫️ The element `length l0` belongs to `nat`.
            - ▫️ The element `length (a :: nil)` belongs to `nat`.
        - ✅ By *IHl*{.just} we have `length (rev l0) = length l0`{.claim}.
      - ✅ Applying *List.length_app*{.just}, we have `length (rev l0 ++ a :: nil) = length (rev l0) + length (a :: nil)`{.claim}.
        - ▫️ The element `rev l0` belongs to `list A`.
        - ▫️ The element `a :: nil` belongs to `list A`.

      Rewriting with `length (rev l0 ++ a :: nil) = length (rev l0) + length (a :: nil)`{.fact} from right to left (eq_ind_r), we get `length (rev l0 ++ a :: nil) = S (length l0)`{.claim}.

  These cases being exhaustive, we deduce `length (rev l) = length l`{.claim}.
