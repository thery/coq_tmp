---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_partial2 (proof in progress)

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H). We prove `x /\ y -> z /\ t`{.claim}.

- Going back to the definition of and (match) in `(x -> z) /\ (y -> t)`{.fact} (H), we prove `x /\ y -> z /\ t`{.claim}:
  - Assume `x -> z`{.hyp} (Hxz), `y -> t`{.hyp} (Hyt) and `x /\ y`{.hyp} (H0).
    - Going back to the definition of and (match) in `x /\ y`{.fact} (H0), we prove `z /\ t`{.claim}:
      - Assume `x`{.hyp} (Hx) and `y`{.hyp} (Hy).
        - We deduce `z`{.claim}.
          - By Hx we have `x`{.claim}.
          - By Hxz we have `x -> z`{.claim}.
        - Prove `t`{.claim}.
        - So by definition of and (conj), we have `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
