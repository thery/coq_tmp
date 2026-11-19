---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
---

# since_demo

Let `a b : Z`{.var}. If `0 < a`{.hyp} and `a < b`{.hyp} then `0 < 2 * b`{.claim}.

- [We have `0 < b`{.claim}]{.p} and hence `0 < b + b`{.claim}.
- So `0 < 2 * b`{.claim}.
