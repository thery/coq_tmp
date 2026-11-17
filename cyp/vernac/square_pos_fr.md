---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: fr
---

# square_pos

Soient `a b : Z`. Si `0 < a < b` alors `a * a < b * b`.

- Il suffit de montrer `0 < b * b - a * a`.
- Ce qui revient à `0 < (b + a) * (b - a)`.
- À partir de `0 < a < b` nous avons `0 < b + a` et `0 < b - a`.
