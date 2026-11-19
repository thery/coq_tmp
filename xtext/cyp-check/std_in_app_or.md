---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-fxtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# in_app_or

Let `A : Type`{.var}. Let `l m : list A`{.var}. Let `a : A`{.var}. We prove `In a (l ++ m) -> In a l \/ In a m`{.claim}.

- We prove `In a (l ++ m) -> In a l \/ In a m` by induction on `l` (list, *list_ind*{.just}):
  - Case 1 (base): we prove `In a (nil ++ m) -> In a nil \/ In a m`{.claim}.
    - Assume `In a m`{.hyp} (H). By definition of or (*or_intror*{.just}), from *H*{.just} we deduce `False \/ In a m`{.claim}.
  - Case 2 (inductive): we prove `forall (a0 : A) (l0 : list A), (In a (l0 ++ m) -> In a l0 \/ In a m) -> In a ((a0 :: l0) ++ m) -> In a (a0 :: l0) \/ In a m`{.claim}.
    - Let `a0 : A`{.var} and `l0 : list A`{.var}; assume by induction hypothesis `In a (l0 ++ m) -> In a l0 \/ In a m`{.hyp} (IHl). Assume `a0 = a \/ In a (l0 ++ m)`{.hyp} (H). We prove `(a0 = a \/ In a l0) \/ In a m` by case analysis on *H*{.just} (or, *or_ind*{.just}):
      - Case 2.1: we prove `a0 = a -> (a0 = a \/ In a l0) \/ In a m`{.claim}.
        - Assume `a0 = a`{.hyp} (H0).
          - By definition of or (*or_introl*{.just}), from *H0*{.just} we deduce `a0 = a \/ In a l0`{.claim}.

          By definition of or (*or_introl*{.just}), we have `(a0 = a \/ In a l0) \/ In a m`{.claim}.
      - Case 2.2: we prove `In a (l0 ++ m) -> (a0 = a \/ In a l0) \/ In a m`{.claim}.
        - Assume `In a (l0 ++ m)`{.hyp} (H0).
          - Applying *IHl*{.just} to *H0*{.just}, we have `In a l0 \/ In a m`{.claim} (H1).
          - We prove `(a0 = a \/ In a l0) \/ In a m` by case analysis on *H1*{.just} (or, *or_ind*{.just}):
            - Case 2.2.1: we prove `In a l0 -> (a0 = a \/ In a l0) \/ In a m`{.claim}.
              - Assume `In a l0`{.hyp} (H10).
                - By definition of or (*or_intror*{.just}), from *H10*{.just} we deduce `a0 = a \/ In a l0`{.claim}.

                By definition of or (*or_introl*{.just}), we have `(a0 = a \/ In a l0) \/ In a m`{.claim}.
            - Case 2.2.2: we prove `In a m -> (a0 = a \/ In a l0) \/ In a m`{.claim}.
              - Assume `In a m`{.hyp} (H10). By definition of or (*or_intror*{.just}), from *H10*{.just} we deduce `(a0 = a \/ In a l0) \/ In a m`{.claim}.

            We have `(a0 = a \/ In a l0) \/ In a m`{.claim} in all cases.

          We have `(a0 = a \/ In a l0) \/ In a m`{.claim}.

      We have `(a0 = a \/ In a l0) \/ In a m`{.claim} in all cases.

  These cases being exhaustive, we deduce `In a (l ++ m) -> In a l \/ In a m`{.claim}.
