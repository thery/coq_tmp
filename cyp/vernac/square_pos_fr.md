---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: fr
---

# square_pos

Soient `a b : Z`{.var}. Si `0 < a < b`{.hyp} alors `a * a < b * b`{.claim}.

- Il suffit de montrer `0 < b * b - a * a`{.claim}.
  - Ce qui revient à `0 < (b + a) * (b - a)`{.claim}.
    - À partir de `0 < a < b`{.fact} nous avons `0 < b + a /\ 0 < b - a`{.claim}.
