---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
---

# since_demo

Let `a b : Z`. If `0 < a` and `a < b` then `0 < 2 * b`.

- We have `0 < b` and hence `0 < b + b`.
- So `0 < 2 * b`.
