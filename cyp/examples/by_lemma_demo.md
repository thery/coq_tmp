---
require: From Stdlib Require Import Reals Lra.
scope: R_scope
by: lra
rules: empty.elpi
---

# by_lemma_demo

Let `a b c d : R`. If `0 <= a <= b` and `0 <= c <= d` then `a * c <= b * d`.

- By monotonicity of the product, we have `a * c <= b * d`. *by Rmult_le_compat*
