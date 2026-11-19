---
require: From Stdlib Require Import Reals.
scope: R_scope
---

<!-- The formulas are those of 2003 (x real, y integer, x ^ y the power
     with an integer exponent); they are not checked here. -->

# exp_pos

Let `x : R`{.var} and `y : Z`{.var}. If `0 < x`{.hyp}, to prove `0 < x ^ y`{.claim}, we have three cases:

- If `0 < y`{.hyp} then `x ^ 1 <= x ^ y`{.claim}.
- If `0 = y`{.hyp} then `x ^ y = 1`{.claim}.
- If `y < 0`{.hyp} then `x ^ y = 1 / x ^ (- y)`{.claim}.
