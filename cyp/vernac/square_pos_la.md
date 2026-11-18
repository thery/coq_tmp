---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: la
---

# square_pos

Sint `a b : Z`. Si `0 < a < b`, tum `a * a < b * b`.

- Sufficit ostendere `0 < b * b - a * a`.
- Quod idem est ac `0 < (b + a) * (b - a)`.
- Quoniam `0 < a < b`, habemus `0 < b + a` et `0 < b - a`.
