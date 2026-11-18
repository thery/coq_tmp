---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: de
---

# square_pos

Seien `a b : Z`. Wenn `0 < a < b`, dann `a * a < b * b`.

- Es genügt zu zeigen `0 < b * b - a * a`.
- Das ist gleichbedeutend mit `0 < (b + a) * (b - a)`.
- Aus `0 < a < b` folgt `0 < b + a` und `0 < b - a`.
