---
require: From Stdlib Require Import Reals Lra.
scope: R_scope
by: lra
rules: named_demo.elpi
---

# named_demo

✅ Let `a b c d : R`{.var}. If `0 <= a <= b`{.hyp} and `0 <= c <= d`{.hyp} then `a * c <= b * d`{.claim}.

- ✅ By *monotonicity*{.just}, `a * c <= b * c`{.claim}.
- ✅ Again `b * c <= b * d`{.claim}, by *monotonicity*{.just}.
