---
require: From Stdlib Require Import Reals. Open Scope R_scope. Require Import XText.reals.
by: tauto | congruence | lia | firstorder | auto
---

# reals_exp_div

Let `x : R`{.var}. We prove `0 < exp x / (1 + x ^ 2)`{.claim}.

- The element `exp x`{.fact} belongs to `R`{.fact}.
- The element `1 + x ^ 2`{.fact} belongs to `R`{.fact}.
- Applying exp_pos to x, we have `0 < exp x`{.claim}.
- Applying Rplus_lt_le_0_compat, we have `0 < 1 + x ^ 2`{.claim}.
  - The element `1`{.fact} belongs to `R`{.fact}.
  - The element `x ^ 2`{.fact} belongs to `R`{.fact}.
  - By Rlt_0_1 we have `0 < 1`{.claim}.
  - Applying pow2_ge_0 to x, we have `0 <= x ^ 2`{.claim}.
- Applying Rdiv_lt_0_compat, we have `0 < exp x / (1 + x ^ 2)`{.claim}.
