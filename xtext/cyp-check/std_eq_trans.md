---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# eq_trans

Let `A : Type`{.var}. Let `x y z : A`{.var}. Assume `x = y`{.hyp} (H) and `y = z`{.hyp} (H0). We prove `x = z`{.claim}.

- Going back to the definition of *eq*{.just} (*match*{.just}) in *H0*{.just}, we prove `x = z`{.claim}:
  - By *H*{.just} we have `x = y`{.claim}.
