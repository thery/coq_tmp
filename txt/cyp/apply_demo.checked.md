---
require: From Stdlib Require Import Reals Lra.
scope: R_scope
by: lra
rules: apply_demo.elpi
---

# apply_demo

✅ Let `a b c d : R`{.var}. If `0 <= a <= b`{.hyp} and `0 <= c <= d`{.hyp} then `a * c <= b * d`{.claim}.

- ✅ By monotonicity of the product, we have `a * c <= b * d`{.claim}.
