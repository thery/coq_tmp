---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# in_or_app

Let `A : Type`{.var}. Let `l m : list A`{.var}. Let `a : A`{.var}. We prove `In a l \/ In a m -> In a (l ++ m)`{.claim}.

- We prove `In a l \/ In a m -> In a (l ++ m)` by induction on *l*{.just} (*list*{.just}, *induction*{.just}):
  - Case 1 (base): we prove `In a nil \/ In a m -> In a (nil ++ m)`{.claim}.
    - Assume `False \/ In a m`{.hyp} (H). We prove `In a m` by case analysis on *H*{.just} (*or*{.just}, *match*{.just}):
      - Case 1.1: we prove `False -> In a m`{.claim}.
        - Assume `False`{.hyp} (H0). By contradiction (*False*{.just}, *match*{.just}), from *H0*{.just} we can deduce `In a m`{.claim}.
      - Case 1.2: we prove `In a m -> In a m`{.claim}.
        - Assume `In a m`{.hyp} (H0). By *H0*{.just} we have `In a m`{.claim}.

      We have `In a m`{.claim} in all cases.
  - Case 2 (inductive): we prove `forall (a0 : A) (l0 : list A), (In a l0 \/ In a m -> In a (l0 ++ m)) -> In a (a0 :: l0) \/ In a m -> In a ((a0 :: l0) ++ m)`{.claim}.
    - Let `a0 : A`{.var}. Let `l0 : list A`{.var}. Assume `In a l0 \/ In a m -> In a (l0 ++ m)`{.hyp} (IHl). By *tauto*{.just} we have `(a0 = a \/ In a l0) \/ In a m -> a0 = a \/ In a (l0 ++ m)`{.claim}.

  These cases being exhaustive, we deduce `In a l \/ In a m -> In a (l ++ m)`{.claim}.
