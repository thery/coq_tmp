---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (h1) and `x /\ y`{.hyp} (h2). We prove `z /\ t`{.claim}.

- Going back to the definition of and (*and_ind*{.just}) in *h1*{.just}, we prove `z /\ t`{.claim}:
  - Assume `x -> z`{.hyp} (i). Assume `y -> t`{.hyp} (j). Going back to the definition of and (*and_ind*{.just}) in *h2*{.just}, we prove `z /\ t`{.claim}:
    - Assume `x`{.hyp} (k). Assume `y`{.hyp} (l).
      - By application, we have `z`{.claim}.
        - By *i*{.just} we have `x -> z`{.claim}.
        - By *k*{.just} we have `x`{.claim}.
      - By application, we have `t`{.claim}.
        - By *j*{.just} we have `y -> t`{.claim}.
        - By *l*{.just} we have `y`{.claim}.

      So by definition of and (*conj*{.just}), we have `z /\ t`{.claim}.
