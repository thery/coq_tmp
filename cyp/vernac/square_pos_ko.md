---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: ko
---

# square_pos

`a b : Z`{.var}라 하자. `0 < a < b`{.hyp}이면 `a * a < b * b`{.claim}이다.

- `0 < b * b - a * a`{.claim}임을 보이면 충분하다.
  - 이는 `0 < (b + a) * (b - a)`{.claim}로 귀결된다.
    - `0 < a < b`{.fact}이므로 `0 < b + a /\ 0 < b - a`{.claim}이다.
