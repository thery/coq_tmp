---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# app_assoc

Let `A : Type`{.var}. Let `l m n : list A`{.var}. We prove `l ++ m ++ n = (l ++ m) ++ n`{.claim}.

- We prove `l ++ m ++ n = (l ++ m) ++ n` by induction on `l` (list, *list_ind*{.just}):
  - Case 1 (base): we prove `nil ++ m ++ n = (nil ++ m) ++ n`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `n = n`{.claim} (H).
    - By application, with *H0*{.just}, we have `n = n -> m ++ n = m ++ n`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `m = m`{.claim} (H0).
      - We have proved `m = m -> n = n -> m ++ n = m ++ n`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `A = A`{.claim} (H1).
        - Assume `m = m`{.hyp} (H00) and `n = n`{.hyp} (H10). By definition of eq (*eq_refl*{.just}), we have `m ++ n = m ++ n`{.claim}.
    - By application, with *H*{.just}, we have `m ++ n = m ++ n`{.claim}.
  - Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ m ++ n = (l0 ++ m) ++ n -> (a :: l0) ++ m ++ n = ((a :: l0) ++ m) ++ n`{.claim}.
    - Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `l0 ++ m ++ n = (l0 ++ m) ++ n`{.hyp} (IHl).
      - By *IHl*{.just} we have `l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim} (H).
      - By application, with *H0*{.just}, we have `l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `a = a`{.claim} (H0).
        - We have proved `a = a -> l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
          - By definition of eq (*eq_refl*{.just}), we have `A = A`{.claim} (H1).
          - Assume `a = a`{.hyp} (H00) and `l0 ++ m ++ n = (l0 ++ m) ++ n`{.hyp} (H10).
            - Applying *f_equal*{.just}, we have `a :: l0 ++ m ++ n = a :: l0 ++ m ++ n`{.claim} (P1.1.1).
              - The element `list A -> list A` belongs to `Type`.
              - The element `list A` belongs to `Type`.
              - The element `fun f : list A -> list A => f (l0 ++ m ++ n)` belongs to `(list A -> list A) -> list A`.
              - The element `cons a` belongs to `list A -> list A`.
              - The element `cons a` belongs to `list A -> list A`.
              - By definition of eq (*eq_refl*{.just}), we have `cons a = cons a`{.claim}.
            - Applying *f_equal*{.just} to *H10*{.just}, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim} (P1.1.2).
              - The element `list A` belongs to `Type`.
              - The element `list A` belongs to `Type`.
              - The element `cons a` belongs to `list A -> list A`.
              - The element `l0 ++ m ++ n` belongs to `list A`.
              - The element `(l0 ++ m) ++ n` belongs to `list A`.
            - The element `list A` belongs to `Type`.
            - The element `a :: l0 ++ m ++ n` belongs to `list A`.
            - The element `a :: l0 ++ m ++ n` belongs to `list A`.
            - The element `a :: (l0 ++ m) ++ n` belongs to `list A`.

            Applying *eq_trans*{.just} to P1.1.1 and P1.1.2, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.

      By application, with *H*{.just}, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.

  These cases being exhaustive, we deduce `l ++ m ++ n = (l ++ m) ++ n`{.claim}.
