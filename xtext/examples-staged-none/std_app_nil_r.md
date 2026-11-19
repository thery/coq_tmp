---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# app_nil_r

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `l ++ nil = l`{.claim}.

- We prove `l ++ nil = l`{.fact} by induction on `l`{.fact} (list, list_ind):
- Case 1 (base): we prove `nil ++ nil = (@nil A)`{.claim}.
  - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H).
  - By definition of eq (eq_refl), we have `nil = (@nil A)`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ nil = l0 -> (a :: l0) ++ nil = a :: l0`{.claim}.
  - Let `a : A`{.var}.
    - Let `l0 : list A`{.var}.
      - Assume `l0 ++ nil = l0`{.hyp} (IHl).
        - By IHl we have `l0 ++ nil = l0`{.claim} (H).
        - By application, we have `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
          - By definition of eq (eq_refl), we have `a = a`{.claim} *by Corelib.Init.Logic.eq_refl* (H0).
          - We have proved `a = a -> l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
            - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H1).
            - Assume `a = a`{.hyp} (H00).
              - Assume `l0 ++ nil = l0`{.hyp} (H10).
                - By application, we have `a :: l0 ++ nil = a :: l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
                  - By application, we have `a :: l0 ++ nil = a :: l0 ++ nil -> a :: l0 ++ nil = a :: l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
                    - By application, we have `forall z : list A, a :: l0 ++ nil = a :: l0 ++ nil -> a :: l0 ++ nil = z -> a :: l0 ++ nil = z`{.claim}.
                      - By application, we have `forall y z : list A, a :: l0 ++ nil = y -> y = z -> a :: l0 ++ nil = z`{.claim}.
                        - By application, we have `forall x y z : list A, x = y -> y = z -> x = z`{.claim}.
                          - By eq_trans we have `forall (A0 : Type) (x y z : A0), x = y -> y = z -> x = z`{.claim}.
                          - The element `list A`{.fact} belongs to `Type`{.fact}.
                        - The element `a :: l0 ++ nil`{.fact} belongs to `list A`{.fact}.
                      - The element `a :: l0 ++ nil`{.fact} belongs to `list A`{.fact}.
                    - The element `a :: l0`{.fact} belongs to `list A`{.fact}.
                  - By application, we have `a :: l0 ++ nil = a :: l0 ++ nil`{.claim}.
                    - By application, we have `cons a = cons a -> a :: l0 ++ nil = a :: l0 ++ nil`{.claim}.
                      - By application, we have `forall y : list A -> list A, cons a = y -> a :: l0 ++ nil = y (l0 ++ nil)`{.claim}.
                        - By application, we have `forall x y : list A -> list A, x = y -> x (l0 ++ nil) = y (l0 ++ nil)`{.claim}.
                          - By application, we have `forall (f : (list A -> list A) -> list A) (x y : list A -> list A), x = y -> f x = f y`{.claim}.
                            - By application, we have `forall (B : Type) (f : (list A -> list A) -> B) (x y : list A -> list A), x = y -> f x = f y`{.claim}.
                              - By f_equal we have `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim}.
                              - The element `list A -> list A`{.fact} belongs to `Type`{.fact}.
                            - The element `list A`{.fact} belongs to `Type`{.fact}.
                          - The element `fun f : list A -> list A => f (l0 ++ nil)`{.fact} belongs to `(list A -> list A) -> list A`{.fact}.
                        - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
                      - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
                    - By definition of eq (eq_refl), we have `cons a = cons a`{.claim} *by Corelib.Init.Logic.eq_refl*.
                - By application, we have `a :: l0 ++ nil = a :: l0`{.claim}.
                  - By application, we have `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
                    - By application, we have `forall y : list A, l0 ++ nil = y -> a :: l0 ++ nil = a :: y`{.claim}.
                      - By application, we have `forall x y : list A, x = y -> a :: x = a :: y`{.claim}.
                        - By application, we have `forall (f : list A -> list A) (x y : list A), x = y -> f x = f y`{.claim}.
                          - By application, we have `forall (B : Type) (f : list A -> B) (x y : list A), x = y -> f x = f y`{.claim}.
                            - By f_equal we have `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim}.
                            - The element `list A`{.fact} belongs to `Type`{.fact}.
                          - The element `list A`{.fact} belongs to `Type`{.fact}.
                        - The element `cons a`{.fact} belongs to `list A -> list A`{.fact}.
                      - The element `l0 ++ nil`{.fact} belongs to `list A`{.fact}.
                    - The element `l0`{.fact} belongs to `list A`{.fact}.
                  - By H10 we have `l0 ++ nil = l0`{.claim}.
                - By application, we have `a :: l0 ++ nil = a :: l0`{.claim}.
              - We have proved `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
          - By H0 we have `a = a`{.claim}.
        - By H we have `l0 ++ nil = l0`{.claim}.
        - By application, we have `a :: l0 ++ nil = a :: l0`{.claim}.
- These cases being exhaustive, we deduce `l ++ nil = l`{.claim} *by Corelib.Init.Datatypes.list_ind*.
