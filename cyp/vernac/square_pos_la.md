---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: la
---

# square_pos

Sint `a b : Z`{.var}. Si `0 < a < b`{.hyp}, tum `a * a < b * b`{.claim}.

- Sufficit ostendere `0 < b * b - a * a`{.claim}.
  - Quod idem est ac `0 < (b + a) * (b - a)`{.claim}.
    - Quoniam `0 < a < b`{.fact}, habemus `0 < b + a /\ 0 < b - a`{.claim}.
