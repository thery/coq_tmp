---
require: From Stdlib Require Import Reals. Open Scope R_scope. Require Import XText.reals.
by: tauto | congruence | lia | firstorder | auto
---

# reals_sqrt_sq

Let `x y : R`{.var}. Assume `0 <= x`{.hyp} (H). We prove `sqrt (x ^ 2) / (Rabs y + 1) = x / (Rabs y + 1)`{.claim}.

- Rewriting with `sqrt x² = x`{.fact} from right to left (eq_ind_r), we get `sqrt x² / (Rabs y + 1) = x / (Rabs y + 1)`{.claim}.
  - By definition of eq (*eq_refl*{.just}), we have `x / (Rabs y + 1) = x / (Rabs y + 1)`{.claim}.
  - Applying *R_sqrt.sqrt_Rsqr*{.just} to x and *H*{.just}, we have `sqrt x² = x`{.claim}.
- Applying *Rfunctions.Rsqr_pow2*{.just} to x, we have `x² = x ^ 2`{.claim}.
- Rewriting with `x² = x ^ 2`{.fact} from left to right (eq_ind), we get `sqrt (x ^ 2) / (Rabs y + 1) = x / (Rabs y + 1)`{.claim}.
