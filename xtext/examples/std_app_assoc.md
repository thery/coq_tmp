---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# app_assoc

Let `A : Type`{.var}. Let `l m n : list A`{.var}. We prove `l ++ m ++ n = (l ++ m) ++ n`{.claim}.

- To prove `l ++ m ++ n = (l ++ m) ++ n`{.fact} by induction (list, list_ind), we generalise it to `forall l0 : list A, l0 ++ m ++ n = (l0 ++ m) ++ n`{.fact}:
- Case 1 (base): we prove `nil ++ m ++ n = (nil ++ m) ++ n`{.claim}.
  - By definition of eq (eq_refl), we have `n = n`{.claim} *by Corelib.Init.Logic.eq_refl* (H).
  - By H we have `n = n`{.claim}.
  - We deduce `n = n -> m ++ n = m ++ n`{.claim}.
    - By definition of eq (eq_refl), we have `m = m`{.claim} *by Corelib.Init.Logic.eq_refl* (H0).
    - By H0 we have `m = m`{.claim}.
    - We have proved `m = m -> n = n -> m ++ n = m ++ n`{.claim}.
      - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H1).
      - Assume `m = m`{.hyp} (H00) and `n = n`{.hyp} (H10).
        - By definition of eq (eq_refl), we have `m ++ n = m ++ n`{.claim} *by Corelib.Init.Logic.eq_refl*.
  - We deduce `m ++ n = m ++ n`{.claim}.
- Case 2 (inductive): we prove `forall (a : A) (l0 : list A), l0 ++ m ++ n = (l0 ++ m) ++ n -> (a :: l0) ++ m ++ n = ((a :: l0) ++ m) ++ n`{.claim}.
  - Let `a : A`{.var}.
  - Let `l0 : list A`{.var}.
  - Assume by induction hypothesis `l0 ++ m ++ n = (l0 ++ m) ++ n`{.hyp} (IHl).
    - By IHl we have `l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim} (H).
    - By H we have `l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim}.
    - We deduce `l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
      - By definition of eq (eq_refl), we have `a = a`{.claim} *by Corelib.Init.Logic.eq_refl* (H0).
      - By H0 we have `a = a`{.claim}.
      - We have proved `a = a -> l0 ++ m ++ n = (l0 ++ m) ++ n -> a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
        - By definition of eq (eq_refl), we have `A = A`{.claim} *by Corelib.Init.Logic.eq_refl* (H1).
        - Assume `a = a`{.hyp} (H00) and `l0 ++ m ++ n = (l0 ++ m) ++ n`{.hyp} (H10).
          - We deduce `a :: l0 ++ m ++ n = a :: l0 ++ m ++ n`{.claim} *by tauto*, that is `a :: l0 ++ m ++ n = a :: l0 ++ m ++ n`{.fact}.
            - By definition of eq (eq_refl), we have `cons a = cons a`{.claim} *by Corelib.Init.Logic.eq_refl*.
            - Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
          - We deduce `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}, that is `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.fact}.
            - By H10 we have `l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim}.
            - Using f_equal we get `forall (A0 B : Type) (f : A0 -> B) (x y : A0), x = y -> f x = f y`{.claim} *by Corelib.Init.Logic.f_equal*.
          - Using eq_trans we get `forall (A0 : Type) (x y z : A0), x = y -> y = z -> x = z`{.claim} *by Corelib.Init.Logic.eq_trans*.
          - We deduce `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
    - We deduce `a :: l0 ++ m ++ n = a :: (l0 ++ m) ++ n`{.claim}.
- These cases being exhaustive, we deduce `forall l0 : list A, l0 ++ m ++ n = (l0 ++ m) ++ n`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- In particular `l ++ m ++ n = (l ++ m) ++ n`{.claim}.
