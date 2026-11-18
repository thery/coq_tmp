---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# in_or_app

✅ Let `A : Type`{.var}. Let `l m : list A`{.var}. Let `a : A`{.var}. We prove `In a l \/ In a m -> In a (l ++ m)`{.claim}.

- ▫️ To prove `In a l \/ In a m -> In a (l ++ m)`{.fact} by induction (list, list_ind), we generalise it to `forall l0 : list A, In a l0 \/ In a m -> In a (l0 ++ m)`{.fact}:
- ✅ Case 1 (base): we prove `In a nil \/ In a m -> In a (nil ++ m)`{.claim}.
  - ▫️ Assume `False \/ In a m`{.hyp} (H).
    - ▫️ We prove `In a m`{.fact} by case analysis on `False \/ In a m`{.fact} (H) (or, or_ind):
    - ✅ Case 1.1: we prove `False -> In a m`{.claim}.
      - ▫️ Assume `False`{.hyp} (H0).
        - ✅ By contradiction (False, False_ind), from `False`{.fact} (H0) we can deduce `In a m`{.claim}.
    - ✅ Case 1.2: we prove `In a m -> In a m`{.claim}.
      - ▫️ Assume `In a m`{.hyp} (H0).
        - ✅ By H0 we have `In a m`{.claim}.
    - ✅ We have `In a m`{.claim} in all cases.
- ✅ Case 2 (inductive): we prove `forall (a0 : A) (l0 : list A), (In a l0 \/ In a m -> In a (l0 ++ m)) -> In a (a0 :: l0) \/ In a m -> In a ((a0 :: l0) ++ m)`{.claim}.
  - ▫️ Let `a0 : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `In a l0 \/ In a m -> In a (l0 ++ m)`{.hyp} (IHl).
    - ✅ We have `(a0 = a \/ In a l0) \/ In a m -> a0 = a \/ In a (l0 ++ m)`{.claim} *by tauto*.
- ✅ These cases being exhaustive, we deduce `forall l0 : list A, In a l0 \/ In a m -> In a (l0 ++ m)`{.claim} *by Corelib.Init.Datatypes.list_ind*.
- ✅ In particular `In a l \/ In a m -> In a (l ++ m)`{.claim}.
