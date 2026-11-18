---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum_partial1 (proof in progress)

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (H). We prove `x /\ y -> z /\ t`{.claim}.

- Going back to the definition of and (match) in `(x -> z) /\ (y -> t)`{.fact} (H), we prove `x /\ y -> z /\ t`{.claim}:
  - Assume `x -> z`{.hyp} (Hxz) and `y -> t`{.hyp} (Hyt) and `x /\ y`{.hyp} (H0).
    - Going back to the definition of and (match) in `x /\ y`{.fact} (H0), we prove `z /\ t`{.claim}:
      - Assume `x`{.hyp} (Hx) and `y`{.hyp} (Hy).
        - Prove `z`{.claim}.
        - Prove `t`{.claim}.
        - So by definition of and (conj), we have `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
