---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: nl
---

# square_pos

Laat `a b : Z`. Als `0 < a < b`, dan `a * a < b * b`.

- Het volstaat te bewijzen dat `0 < b * b - a * a`.
- Dit komt neer op `0 < (b + a) * (b - a)`.
- Omdat `0 < a < b`, hebben we `0 < b + a` en `0 < b - a`.
