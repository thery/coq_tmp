---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: ar
---

# square_pos

ليكن `a b : Z`. إذا كان `0 < a < b` فإن `a * a < b * b`.

- يكفي أن نثبت أن `0 < b * b - a * a`.
- وهذا يكافئ `0 < (b + a) * (b - a)`.
- بما أن `0 < a < b` فإن `0 < b + a` و `0 < b - a`.
