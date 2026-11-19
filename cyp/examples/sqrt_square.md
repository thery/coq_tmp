---
require: From Stdlib Require Import Reals Lra.
scope: R_scope
by: congruence | lra
---

# sqrt_square

Let `x y : R`{.var}. If `0 <= x`{.hyp} and `0 < y`{.hyp} then `sqrt (x ^ 2) / y + Rabs (- x) = x / y + x`{.claim}.

- First `sqrt (x ^ 2) = x`{.claim}, by *sqrt_pow2*{.just}.
- So `sqrt (x ^ 2) / y = x / y`{.claim}.
- The absolute value of the opposite is `Rabs (- x) = Rabs x`{.claim} (*Rabs_Ropp*{.just}).
- As `0 <= x`{.fact}, we have `Rabs x = x`{.claim} by *Rabs_pos_eq*{.just}.
- Hence `sqrt (x ^ 2) / y + Rabs (- x) = x / y + x`{.claim}.
