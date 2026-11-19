---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: ar
---

# square_pos

ليكن `a b : Z`{.var}. إذا كان `0 < a < b`{.hyp} فإن `a * a < b * b`{.claim}.

- يكفي أن نثبت أن `0 < b * b - a * a`{.claim}.
  - وهذا يكافئ `0 < (b + a) * (b - a)`{.claim}.
    - بما أن `0 < a < b`{.fact} فإن `0 < b + a /\ 0 < b - a`{.claim}.
