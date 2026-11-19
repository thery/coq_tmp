---
require: From Stdlib Require Import Reals. Open Scope R_scope. Require Import XText.reals.
by: tauto | congruence | lia | firstorder | auto
---

# reals_exp_div

Let `x : R`{.var}. We prove `0 < exp x / (1 + x ^ 2)`{.claim}.

- The element `exp x` belongs to `R`.
- The element `1 + x ^ 2` belongs to `R`.
- Applying *Exp_prop.exp_pos*{.just} to x, we have `0 < exp x`{.claim}.
- Applying *RIneq.Rplus_lt_le_0_compat*{.just}, we have `0 < 1 + x ^ 2`{.claim}.
  - The element `1` belongs to `R`.
  - The element `x ^ 2` belongs to `R`.
  - By *RIneq.Rlt_0_1*{.just} we have `0 < 1`{.claim}.
  - Applying *Ratan.pow2_ge_0*{.just} to x, we have `0 <= x ^ 2`{.claim}.
- Applying *RIneq.Rdiv_lt_0_compat*{.just}, we have `0 < exp x / (1 + x ^ 2)`{.claim}.
