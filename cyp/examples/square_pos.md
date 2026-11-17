---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia | nia
---

# square_pos

Let `a b : Z`. If `0 < a < b` then `a * a < b * b`.

- It is equivalent to prove `0 < b * b - a * a`.
- That can also be written as `0 < (b + a) * (b - a)`.
- From `0 < a < b` we have `0 < b + a` and `0 < b - a`.
- Hence `0 < b - a + 1`. *by lia*
- So `0 < a - b`, a wrong step on purpose.
