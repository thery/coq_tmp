---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# app_assoc

Let `A : Type`{.var}. Let `l m n : list A`{.var}. We prove `l ++ m ++ n = (l ++ m) ++ n`{.claim}.

- To prove `l ++ m ++ n = (l ++ m) ++ n`{.fact} by induction (list, list_ind), we generalise it to `forall l0 : list A, l0 ++ m ++ n = (l0 ++ m) ++ n`{.fact}:
- Case 1 (base): we prove `nil ++ m ++ n = (nil ++ m) ++ n`{.claim}.
  - By definition of eq (eq_refl), we have `n = n`{.claim} *by Corelib.Init.Logic.eq_refl* (H).
  - By application, with H0, we have `n = n -> m ++ n = m ++ n`{.claim}.
    - By definition of eq (eq_refl), we have `m = m`{.claim} *by Corelib.Init.Logic.eq_refl* (H0).
    - We have proved `m = m -> n = n -> m ++ n = m ++ n`{.claim}.
      - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H1).
      - Assume `m = m`{.hyp} (H00) and `n = n`{.hyp} (H10).
        - By definition of eq (eq_refl), we have `m ++ n = m ++ n`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - By application, with H, we have `m ++ n = m ++ n`{.claim}.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ m ++ n = (l0 ++ m) ++ n -> (a :: l0) ++ m ++ n = ((a :: l0) ++ m) ++ n`{.claim}.
  - Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `l0 ++ m ++ n = (l0 ++ m) ++ n`{.hyp} (IHl).
    - By IHl we have `l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim} (H).
    - By application, with H0, we have `l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
      - By definition of eq (eq_refl), we have `a = a`{.claim} *by Corelib.Init.Logic.eq_refl* (H0).
      - We have proved `a = a -> l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
        - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H1).
        - Assume `a = a`{.hyp} (H00) and `l0 ++ m ++ n = (l0 ++ m) ++ n`{.hyp} (H10).
          - The element `list A`{.fact} belongs to `Type`{.fact}.
          - The element `a :: l0 ++ m ++ n`{.fact} belongs to `list A`{.fact}.
          - The element `a :: l0 ++ m ++ n`{.fact} belongs to `list A`{.fact}.
          - The element `a :: (l0 ++ m) ++ n`{.fact} belongs to `list A`{.fact}.
          - Applying f_equal, we have `a :: l0 ++ m ++ n = a :: l0 ++ m ++ n`{.claim}.
            - The element `list A -> list A`{.fact} belongs to `Type`{.fact}.
            - The element `list A`{.fact} belongs to `Type`{.fact}.
            - The element `fun f : list A -> list A => f (l0 ++ m ++ n)`{.fact} belongs to `(list A -> list A) -> list A`{.fact}.
            - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
            - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
            - By definition of eq (eq_refl), we have `cons a = cons a`{.claim} *by Corelib.Init.Logic.eq_refl*.
          - Applying f_equal to H10, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
            - The element `list A`{.fact} belongs to `Type`{.fact}.
            - The element `list A`{.fact} belongs to `Type`{.fact}.
            - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
            - The element `l0 ++ m ++ n`{.fact} belongs to `list A`{.fact}.
            - The element `(l0 ++ m) ++ n`{.fact} belongs to `list A`{.fact}.
          - Applying eq_trans, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
    - By application, with H, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
- These cases being exhaustive, we deduce `forall l0 : list A, l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `l ++ m ++ n = (l ++ m) ++ n`{.claim}.
