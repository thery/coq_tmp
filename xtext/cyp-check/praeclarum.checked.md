---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# praeclarum

✅ Let `x y z t : Prop`{.var}. Assume `(x -> z) /\ (y -> t)`{.hyp} (h1) and `x /\ y`{.hyp} (h2). We prove `z /\ t`{.claim}.

- ✅ Going back to the definition of *and*{.just} (*match*{.just}) in *h1*{.just}, we prove `z /\ t`{.claim}:
  - ✅ Assume `x -> z`{.hyp} (i) and `y -> t`{.hyp} (j). Going back to the definition of *and*{.just} (*match*{.just}) in *h2*{.just}, we prove `z /\ t`{.claim}:
    - ✅ Assume `x`{.hyp} (k) and `y`{.hyp} (l).
      - ✅ Applying *i*{.just} to *k*{.just}, we have `z`{.claim}.
      - ✅ Applying *j*{.just} to *l*{.just}, we have `t`{.claim}.

      So by definition of and (*conj*{.just}), we have `z /\ t`{.claim}.
