---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (h1) and `x /\ y`{.hyp} (h2). We prove `z /\ t`{.claim}.

- Going back to the definition of and (and_ind) in `(x -> z) /\ (y -> t)`{.fact} (h1), we prove `z /\ t`{.claim}:
  - Assume `x -> z`{.hyp} (i) and `y -> t`{.hyp} (j).
    - Going back to the definition of and (and_ind) in `x /\ y`{.fact} (h2), we prove `z /\ t`{.claim}:
      - Assume `x`{.hyp} (k) and `y`{.hyp} (l).
        - We deduce `z`{.claim}.
          - By k we have `x`{.claim}.
          - By i we have `x -> z`{.claim}.
        - We deduce `t`{.claim}.
          - By l we have `y`{.claim}.
          - By j we have `y -> t`{.claim}.
        - So by definition of and (conj), we have `z /\ t`{.claim} *by Corelib.Init.Logic.conj*.
