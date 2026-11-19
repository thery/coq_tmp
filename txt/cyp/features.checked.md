---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
rules: features_rules1.v features_rules2.v
---

# features

✅ Let `a b : Z`. If `0 < a < b` then `0 < 2 * b - a`.

- ▫️ Let `u := b - a`.
- ✅ It is enough to check all the cases, so we have `0 < u`.
- ✅ Hence `0 < 2 * b - a`.
