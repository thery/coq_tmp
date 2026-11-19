---
require: From Stdlib Require Import Reals Lra Lia.
scope: R_scope
by: lra
rules: rules_demo.elpi
---

# product_le

✅ Let `a b c d : R`. If `0 <= a <= b` and `0 <= c <= d` then `a * c <= b * d`.

- ✅ From `0 <= a <= b` we have `a * c <= b * c`.
- ✅ Since `c <= d` and `0 <= b` we have `b * c <= b * d`.
