---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: de
---

# square_pos

Seien `a b : Z`{.var}. Wenn `0 < a < b`{.hyp}, dann `a * a < b * b`{.claim}.

- Es genügt zu zeigen `0 < b * b - a * a`{.claim}.
  - Das ist gleichbedeutend mit `0 < (b + a) * (b - a)`{.claim}.
    - Aus `0 < a < b`{.fact} folgt `0 < b + a /\ 0 < b - a`{.claim}.
