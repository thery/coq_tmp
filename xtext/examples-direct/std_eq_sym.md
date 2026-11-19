---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# eq_sym

Let `A : Type`{.var}. Let `x y : A`{.var}. Assume `x = y`{.hyp} (H). We prove `y = x`{.claim}.

- Going back to the definition of *eq*{.just} (*match*{.just}) in *H*{.just}, we prove `y = x`{.claim}:
  - By definition of eq (*eq_refl*{.just}), we have `x = x`{.claim}.
