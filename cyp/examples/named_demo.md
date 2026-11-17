---
require: From Stdlib Require Import Reals Lra.
scope: R_scope
by: lra
rules: named_demo.elpi
---

# named_demo

Let `a b c d : R`. If `0 <= a <= b` and `0 <= c <= d` then `a * c <= b * d`.

- By monotonicity, `a * c <= b * c`. *by monotonicity*
- Again `b * c <= b * d`. *by monotonicity*
