---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# app_nil_r

Let `A : Type`{.var}. Let `l : list A`{.var}. We prove `l ++ nil = l`{.claim}.

- To prove `l ++ nil = l`{.fact} by induction (list, list_ind), we generalise it to `forall l0 : list A, l0 ++ nil = l0`{.fact}:
- Case 1 (base): we prove `nil ++ nil = (@nil A)`{.claim}.
  - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H).
  - By definition of eq (eq_refl), we have `nil = (@nil A)`{.claim} *by Corelib.Init.Logic.eq_refl*.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ nil = l0 -> (a :: l0) ++ nil = a :: l0`{.claim}.
  - Let `a : A`{.var}.
  - Let `l0 : list A`{.var}.
  - Assume by induction hypothesis `l0 ++ nil = l0`{.hyp} (IHl).
    - By IHl we have `l0 ++ nil = l0`{.claim} (H).
    - By H we have `l0 ++ nil = l0`{.claim}.
    - We deduce `l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
      - By definition of eq (eq_refl), we have `a = a`{.claim} *by Corelib.Init.Logic.eq_refl* (H0).
      - By H0 we have `a = a`{.claim}.
      - We have proved `a = a -> l0 ++ nil = l0 -> a :: l0 ++ nil = a :: l0`{.claim}.
        - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H1).
        - Assume `a = a`{.hyp} (H00) and `l0 ++ nil = l0`{.hyp} (H10).
          - By definition of eq (eq_refl), we have `cons a = cons a`{.claim} *by Corelib.Init.Logic.eq_refl*.
          - Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
          - By H10 we have `l0 ++ nil = l0`{.claim}.
          - Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
          - Using eq_trans we get `forall (A0 : Type) (x y z : A0), x = y -> y = z -> x = z`{.claim} *by Corelib.Init.Logic.eq_trans*.
          - We deduce `a :: l0 ++ nil = a :: l0`{.claim} *by congruence*.
    - We deduce `a :: l0 ++ nil = a :: l0`{.claim}.
- These cases being exhaustive, we deduce `forall l0 : list A, l0 ++ nil = l0`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `l ++ nil = l`{.claim}.
