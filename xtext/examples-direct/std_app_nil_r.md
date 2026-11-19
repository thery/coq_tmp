---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# app_nil_r

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `l ++ nil = l`{.claim}.

- We prove `l ++ nil = l` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - Case 1 (base): we prove `nil ++ nil = (@nil A)`{.claim}.
    - By definition of eq (*eq_refl*{.just}), we have `A = A`{.claim} (H).
    - By definition of eq (*eq_refl*{.just}), we have `nil = (@nil A)`{.claim}.
  - Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ nil = l0 -> (a :: l0) ++ nil = a :: l0`{.claim}.
    - Let `a : A`{.var}. Let `l0 : list A`{.var}. Assume by induction hypothesis `l0 ++ nil = l0`{.hyp} (IHl).
      - By *IHl*{.just} we have `l0 ++ nil = l0`{.claim} (H).
      - By *H*{.just} we have `l0 ++ nil = l0`{.claim}.
      - We deduce `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
        - By definition of eq (*eq_refl*{.just}), we have `a = a`{.claim} (H0).
        - By *H0*{.just} we have `a = a`{.claim}.
        - We have proved `a = a -> l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
          - By definition of eq (*eq_refl*{.just}), we have `A = A`{.claim} (H1).
          - Assume `a = a`{.hyp} (H00) and `l0 ++ nil = l0`{.hyp} (H10).
            - By *tauto*{.just} we deduce `a :: l0 ++ nil = a :: l0 ++ nil`, that is `a :: l0 ++ nil = a :: l0 ++ nil`{.claim}.
              - By definition of eq (*eq_refl*{.just}), we have `cons a = cons a`{.claim}.
              - Using *f_equal*{.just} we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim}.
            - We deduce `a :: l0 ++ nil = a :: l0`, that is `a :: l0 ++ nil = a :: l0`{.claim}.
              - By *H10*{.just} we have `l0 ++ nil = l0`{.claim}.
              - Using *f_equal*{.just} we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim}.
            - Using *eq_trans*{.just} we get `forall (A0 : Type) (x y z : A0), x = y -> y = z -> x = z`{.claim}.

            We deduce `a :: l0 ++ nil = a :: l0`{.claim}.

      We deduce `a :: l0 ++ nil = a :: l0`{.claim}.

  These cases being exhaustive, we deduce `l ++ nil = l`{.claim}.
