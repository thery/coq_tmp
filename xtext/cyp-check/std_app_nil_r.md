---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# app_nil_r

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `l ++ nil = l`{.claim}.

- We prove `l ++ nil = l`{.fact} by induction on `l`{.fact} (list, list_ind):
- Case 1 (base): we prove `nil ++ nil = (@nil A)`{.claim}.
  - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H).
  - By definition of eq (eq_refl), we have `nil = (@nil A)`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ nil = l0 -> (a :: l0) ++ nil = a :: l0`{.claim}.
  - Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `l0 ++ nil = l0`{.hyp} (IHl).
    - By IHl we have `l0 ++ nil = l0`{.claim} (H).
    - By application, with H0, we have `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
      - By definition of eq (eq_refl), we have `a = a`{.claim} *by Corelib.Init.Logic.eq_refl* (H0).
      - We have proved `a = a -> l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
        - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H1).
        - Assume `a = a`{.hyp} (H00) and `l0 ++ nil = l0`{.hyp} (H10).
          - The element `list A`{.fact} belongs to `Type`{.fact}.
          - The element `a :: l0 ++ nil`{.fact} belongs to `list A`{.fact}.
          - The element `a :: l0 ++ nil`{.fact} belongs to `list A`{.fact}.
          - The element `a :: l0`{.fact} belongs to `list A`{.fact}.
          - Applying f_equal, we have `a :: l0 ++ nil = a :: l0 ++ nil`{.claim}.
            - The element `list A -> list A`{.fact} belongs to `Type`{.fact}.
            - The element `list A`{.fact} belongs to `Type`{.fact}.
            - The element `fun f : list A -> list A => f (l0 ++ nil)`{.fact} belongs to `(list A -> list A) -> list A`{.fact}.
            - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
            - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
            - By definition of eq (eq_refl), we have `cons a = cons a`{.claim} *by Corelib.Init.Logic.eq_refl*.
          - Applying f_equal, we have `a :: l0 ++ nil = a :: l0`{.claim}.
            - The element `list A`{.fact} belongs to `Type`{.fact}.
            - The element `list A`{.fact} belongs to `Type`{.fact}.
            - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
            - The element `l0 ++ nil`{.fact} belongs to `list A`{.fact}.
            - The element `l0`{.fact} belongs to `list A`{.fact}.
            - By H10 we have `l0 ++ nil = l0`{.claim}.
          - Applying eq_trans, we have `a :: l0 ++ nil = a :: l0`{.claim}.
    - By application, with H, we have `a :: l0 ++ nil = a :: l0`{.claim}.
- These cases being exhaustive, we deduce `l ++ nil = l`{.claim} *by Corelib.Init.Datatypes.list_ind*.
