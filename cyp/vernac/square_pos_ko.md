---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: ko
---

# square_pos

`a b : Z`라 하자. `0 < a < b`이면 `a * a < b * b`이다.

- `0 < b * b - a * a`임을 보이면 충분하다.
- 이는 `0 < (b + a) * (b - a)`로 귀결된다.
- `0 < a < b`이므로 `0 < b + a`이고 `0 < b - a`이다.
