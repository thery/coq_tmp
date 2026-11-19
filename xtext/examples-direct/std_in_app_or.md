---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# in_app_or

Let `A : Type`{.var}. Let `l m : list A`{.var}. Let `a : A`{.var}. We prove `In a (l ++ m) -> In a l \/ In a m`{.claim}.

- We prove `In a (l ++ m) -> In a l \/ In a m`{.fact} by induction on `l`{.fact} (list, list_ind):
- Case 1 (base): we prove `In a (nil ++ m) -> In a nil \/ In a m`{.claim}.
  - Assume `In a m`{.hyp} (H).
    - By definition of or (or_intror), from `In a m`{.fact} (H) we deduce `False \/ In a m`{.claim} *by Corelib.Init.Logic.or_intror*.
- Case 2 (inductive): we prove `forall (a0 : A) (l0 : list A), (In a (l0 ++ m) -> In a l0 \/ In a m) -> In a ((a0 :: l0) ++ m) -> In a (a0 :: l0) \/ In a m`{.claim}.
  - Let `a0 : A`{.var}.
  - Let `l0 : list A`{.var}.
  - Assume by induction hypothesis `In a (l0 ++ m) -> In a l0 \/ In a m`{.hyp} (IHl).
    - Assume `a0 = a \/ In a (l0 ++ m)`{.hyp} (H).
      - We prove `(a0 = a \/ In a l0) \/ In a m`{.fact} by case analysis on `a0 = a \/ In a (l0 ++ m)`{.fact} (H) (or, or_ind):
      - Case 2.1: we prove `a0 = a -> (a0 = a \/ In a l0) \/ In a m`{.claim}.
        - Assume `a0 = a`{.hyp} (H0).
          - By definition of or (or_introl), from `a0 = a`{.fact} (H0) we deduce `a0 = a \/ In a l0`{.claim} *by Corelib.Init.Logic.or_introl*.
          - By definition of or (or_introl), we have `(a0 = a \/ In a l0) \/ In a m`{.claim} *by Corelib.Init.Logic.or_introl*.
      - Case 2.2: we prove `In a (l0 ++ m) -> (a0 = a \/ In a l0) \/ In a m`{.claim}.
        - Assume `In a (l0 ++ m)`{.hyp} (H0).
          - We deduce `In a l0 \/ In a m`{.claim} (H1).
            - By H0 we have `In a (l0 ++ m)`{.claim}.
            - By IHl we have `In a (l0 ++ m) -> In a l0 \/ In a m`{.claim}.
          - We prove `(a0 = a \/ In a l0) \/ In a m`{.fact} by case analysis on `In a l0 \/ In a m`{.fact} (H1) (or, or_ind):
          - Case 2.2.1: we prove `In a l0 -> (a0 = a \/ In a l0) \/ In a m`{.claim}.
            - Assume `In a l0`{.hyp} (H10).
              - By definition of or (or_intror), from `In a l0`{.fact} (H10) we deduce `a0 = a \/ In a l0`{.claim} *by Corelib.Init.Logic.or_intror*.
              - By definition of or (or_introl), we have `(a0 = a \/ In a l0) \/ In a m`{.claim} *by Corelib.Init.Logic.or_introl*.
          - Case 2.2.2: we prove `In a m -> (a0 = a \/ In a l0) \/ In a m`{.claim}.
            - Assume `In a m`{.hyp} (H10).
              - By definition of or (or_intror), from `In a m`{.fact} (H10) we deduce `(a0 = a \/ In a l0) \/ In a m`{.claim} *by Corelib.Init.Logic.or_intror*.
          - We have `(a0 = a \/ In a l0) \/ In a m`{.claim} in all cases.
      - We have `(a0 = a \/ In a l0) \/ In a m`{.claim} in all cases.
- These cases being exhaustive, we deduce `In a (l ++ m) -> In a l \/ In a m`{.claim} *by Corelib.Init.Datatypes.list_ind*.
