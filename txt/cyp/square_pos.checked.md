---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia | nia
---

# square_pos

✅ Let `a b : Z`{.var}. If `0 < a < b`{.hyp} then `a * a < b * b`{.claim}.

- ✅ It is equivalent to prove `0 < b * b - a * a`{.claim}.
  - ✅ That can also be written as `0 < (b + a) * (b - a)`{.claim}.
    - ✅ From `0 < a < b`{.fact} we have `0 < b + a /\ 0 < b - a`{.claim}.
- ✅ Hence `0 < b - a + 1`{.claim} by *lia*{.just}.
- ❌ So `0 < a - b`{.claim}, a wrong step on purpose.

  <details><summary>not proved: 0 < a - b</summary></details>

- ✅ A tagged formula `0 <= a * a`{.claim}, whatever the words before it.
