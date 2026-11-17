---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# eq_trans

Let `A : Type`{.var}. Let `x y z : A`{.var}. Assume `x = y`{.hyp} (H) and `y = z`{.hyp} (H0). We prove `x = z`{.claim}.

- Going back to the definition of eq (match) in `y = z`{.fact} (H0), we prove `x = z`{.claim}:
  - By H we have `x = y`{.claim}.
