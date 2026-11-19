---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# app_nil_r

✅ Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `l ++ nil = l`{.claim}.

- ✅ We prove `l ++ nil = l` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - ✅ Case 1 (base): we prove `nil ++ nil = (@nil A)`{.claim}.
    - ✅ By definition of eq (*eq_refl*{.just}), we have `A = A`{.claim} (H).
    - ✅ By definition of eq (*eq_refl*{.just}), we have `nil = (@nil A)`{.claim}.
  - ✅ Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ nil = l0 -> (a :: l0) ++ nil = a :: l0`{.claim}.
    - ✅ Let `a : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `l0 ++ nil = l0`{.hyp} (IHl).
      - ✅ By *IHl*{.just} we have `l0 ++ nil = l0`{.claim} (H).
      - ✅ By application, with *H0*{.just}, we have `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
        - ✅ By definition of eq (*eq_refl*{.just}), we have `a = a`{.claim} (H0).
        - ✅ We have proved `a = a -> l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
          - ✅ By definition of eq (*eq_refl*{.just}), we have `A = A`{.claim} (H1).
          - ✅ Assume `a = a`{.hyp} (H00) and `l0 ++ nil = l0`{.hyp} (H10).
            - ▫️ The element `list A` belongs to `Type`.
            - ▫️ The element `a :: l0 ++ nil` belongs to `list A`.
            - ▫️ The element `a :: l0 ++ nil` belongs to `list A`.
            - ▫️ The element `a :: l0` belongs to `list A`.
            - ✅ Applying *f_equal*{.just}, we have `a :: l0 ++ nil = a :: l0 ++ nil`{.claim}.
              - ▫️ The element `list A -> list A` belongs to `Type`.
              - ▫️ The element `list A` belongs to `Type`.
              - ▫️ The element `fun f : list A -> list A => f (l0 ++ nil)` belongs to `(list A -> list A) -> list A`.
              - ▫️ The element `cons a` belongs to `list A -> list A`.
              - ▫️ The element `cons a` belongs to `list A -> list A`.
              - ✅ By definition of eq (*eq_refl*{.just}), we have `cons a = cons a`{.claim}.
            - ✅ Applying *f_equal*{.just}, we have `a :: l0 ++ nil = a :: l0`{.claim}.
              - ▫️ The element `list A` belongs to `Type`.
              - ▫️ The element `list A` belongs to `Type`.
              - ▫️ The element `cons a` belongs to `list A -> list A`.
              - ▫️ The element `l0 ++ nil` belongs to `list A`.
              - ✅ By *H10*{.just} we have `l0 ++ nil = l0`{.claim}.

            Applying *eq_trans*{.just}, we have `a :: l0 ++ nil = a :: l0`{.claim}.

      By application, with *H*{.just}, we have `a :: l0 ++ nil = a :: l0`{.claim}.

  These cases being exhaustive, we deduce `l ++ nil = l`{.claim}.
