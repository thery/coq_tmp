---
require: From Stdlib Require Import Reals Lra Lia.
scope: R_scope
by: lra
rules: rules_demo.elpi
---

# product_le

✅ Let `a b c d : R`{.var}. If `0 <= a <= b`{.hyp} and `0 <= c <= d`{.hyp} then `a * c <= b * d`{.claim}.

- ✅ From `0 <= a <= b`{.fact} we have `a * c <= b * c`{.claim}.
- ✅ Since `c <= d` and `0 <= b` (plain words: neither is a hypothesis as written) we have `b * c <= b * d`{.claim}.
