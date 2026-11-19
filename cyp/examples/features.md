---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
rules: features_rules1.v features_rules2.v
---

# features

Let `a b : Z`{.var}. If `0 < a < b`{.hyp} then `0 < 2 * b - a`{.claim}.

- Let `u := b - a`{.var}.
  - It is enough to check all the cases, so we have `0 < u`{.claim}.

  Hence `0 < 2 * b - a`{.claim}.
