---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (h1) and `x /\ y`{.hyp} (h2). We prove `z /\ t`{.claim}.

- Going back to the definition of and (and_ind) in `(x -> z) /\ (y -> t)`{.fact} (h1), we prove `z /\ t`{.claim}:
  - Assume `x -> z`{.hyp} (i).
    - Assume `y -> t`{.hyp} (j).
      - Going back to the definition of and (and_ind) in `x /\ y`{.fact} (h2), we prove `z /\ t`{.claim}:
        - Assume `x`{.hyp} (k).
          - Assume `y`{.hyp} (l).
            - By application, we have `z`{.claim}.
              - By i we have `x -> z`{.claim}.
              - By k we have `x`{.claim}.
            - By application, we have `t`{.claim}.
              - By j we have `y -> t`{.claim}.
              - By l we have `y`{.claim}.
            - So by definition of and (conj), we have `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
