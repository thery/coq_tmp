---
require: From Stdlib Require Import Reals Lra.
scope: R_scope
by: congruence | lra
---

# sqrt_square

✅ Let `x y : R`. If `0 <= x` and `0 < y` then `sqrt (x ^ 2) / y + Rabs (- x) = x / y + x`.

- ✅ First `sqrt (x ^ 2) = x`. *by sqrt_pow2*
- ✅ So `sqrt (x ^ 2) / y = x / y`.
- ✅ The absolute value of the opposite is `Rabs (- x) = Rabs x`. *by Rabs_Ropp*
- ✅ As `0 <= x`, we have `Rabs x = x`. *by Rabs_pos_eq*
- ✅ Hence `sqrt (x ^ 2) / y + Rabs (- x) = x / y + x`.
