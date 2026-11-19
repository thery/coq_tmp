---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia | nia
---

# square_pos

Let `a b : Z`{.var}. If `0 < a < b`{.hyp} then `a * a < b * b`{.claim}.

- It is equivalent to prove `0 < b * b - a * a`{.claim}.
  - That can also be written as `0 < (b + a) * (b - a)`{.claim}.
    - From `0 < a < b`{.fact} we have `0 < b + a /\ 0 < b - a`{.claim}.
