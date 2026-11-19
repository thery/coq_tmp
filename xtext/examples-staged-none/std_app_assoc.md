---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# app_assoc

Let `A : Type`{.var}. Let `l m n : list A`{.var}. We prove `l ++ m ++ n = (l ++ m) ++ n`{.claim}.

- We prove `l ++ m ++ n = (l ++ m) ++ n` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - Case 1 (base): we prove `nil ++ m ++ n = (nil ++ m) ++ n`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `n = n`{.claim} (H).
    - By application, we have `n = n -> m ++ n = m ++ n`{.claim}.
      - By definition of eq (*eq_refl*{.just}), we have `m = m`{.claim} (H0).
      - We have proved `m = m -> n = n -> m ++ n = m ++ n`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `A = A`{.claim} (H1).
        - Assume `m = m`{.hyp} (H00).
          - Assume `n = n`{.hyp} (H10). By definition of eq (*eq_refl*{.just}), we have `m ++ n = m ++ n`{.claim}.

          We have proved `n = n -> m ++ n = m ++ n`{.claim}.
      - By *H0*{.just} we have `m = m`{.claim}.
    - By *H*{.just} we have `n = n`{.claim}.
    - By application, we have `m ++ n = m ++ n`{.claim}.
  - Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ m ++ n = (l0 ++ m) ++ n -> (a :: l0) ++ m ++ n = ((a :: l0) ++ m) ++ n`{.claim}.
    - Let `a : A`{.var}. Let `l0 : list A`{.var}. Assume `l0 ++ m ++ n = (l0 ++ m) ++ n`{.hyp} (IHl).
      - By *IHl*{.just} we have `l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim} (H).
      - By application, we have `l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `a = a`{.claim} (H0).
        - We have proved `a = a -> l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
          - By definition of eq (*eq_refl*{.just}), we have `A = A`{.claim} (H1).
          - Assume `a = a`{.hyp} (H00).
            - Assume `l0 ++ m ++ n = (l0 ++ m) ++ n`{.hyp} (H10).
              - By application, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
                - By application, we have `a :: l0 ++ m ++ n = a :: l0 ++ m ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
                  - By application, we have `forall z : list A, a :: l0 ++ m ++ n = a :: l0 ++ m ++ n -> a :: l0 ++ m ++ n = z -> a :: l0 ++ m ++ n = z`{.claim}.
                    - By application, we have `forall y z : list A, a :: l0 ++ m ++ n = y -> y = z -> a :: l0 ++ m ++ n = z`{.claim}.
                      - By application, we have `forall x y z : list A, x = y -> y = z -> x = z`{.claim}.
                        - By *eq_trans*{.just} we have `forall (A0 : Type) (x y z : A0), x = y -> y = z -> x = z`{.claim}.
                        - The element `list A` belongs to `Type`.
                      - The element `a :: l0 ++ m ++ n` belongs to `list A`.
                    - The element `a :: l0 ++ m ++ n` belongs to `list A`.
                  - The element `a :: (l0 ++ m) ++ n` belongs to `list A`.
                - By application, we have `a :: l0 ++ m ++ n = a :: l0 ++ m ++ n`{.claim}.
                  - By application, we have `cons a = cons a -> a :: l0 ++ m ++ n = a :: l0 ++ m ++ n`{.claim}.
                    - By application, we have `forall y : list A -> list A, cons a = y -> a :: l0 ++ m ++ n = y (l0 ++ m ++ n)`{.claim}.
                      - By application, we have `forall x y : list A -> list A, x = y -> x (l0 ++ m ++ n) = y (l0 ++ m ++ n)`{.claim}.
                        - By application, we have `forall (f : (list A -> list A) -> list A) (x y : list A -> list A), x = y -> f x = f y`{.claim}.
                          - By application, we have `forall (B : Type) (f : (list A -> list A) -> B) (x y : list A -> list A), x = y -> f x = f y`{.claim}.
                            - By *f_equal*{.just} we have `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim}.
                            - The element `list A -> list A` belongs to `Type`.
                          - The element `list A` belongs to `Type`.
                        - The element `fun f : list A -> list A => f (l0 ++ m ++ n)` belongs to `(list A -> list A) -> list A`.
                      - The element `cons a` belongs to `list A -> list A`.
                    - The element `cons a` belongs to `list A -> list A`.
                  - By definition of eq (*eq_refl*{.just}), we have `cons a = cons a`{.claim}.
              - By application, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
                - By application, we have `l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
                  - By application, we have `forall y : list A, l0 ++ m ++ n = y -> a :: l0 ++ m ++ n = a :: y`{.claim}.
                    - By application, we have `forall x y : list A, x = y -> a :: x = a :: y`{.claim}.
                      - By application, we have `forall (f : list A -> list A) (x y : list A), x = y -> f x = f y`{.claim}.
                        - By application, we have `forall (B : Type) (f : list A -> B) (x y : list A), x = y -> f x = f y`{.claim}.
                          - By *f_equal*{.just} we have `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim}.
                          - The element `list A` belongs to `Type`.
                        - The element `list A` belongs to `Type`.
                      - The element `cons a` belongs to `list A -> list A`.
                    - The element `l0 ++ m ++ n` belongs to `list A`.
                  - The element `(l0 ++ m) ++ n` belongs to `list A`.
                - By *H10*{.just} we have `l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim}.

              By application, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.

            We have proved `l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
        - By *H0*{.just} we have `a = a`{.claim}.
      - By *H*{.just} we have `l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim}.

      By application, we have `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.

  These cases being exhaustive, we deduce `l ++ m ++ n = (l ++ m) ++ n`{.claim}.
