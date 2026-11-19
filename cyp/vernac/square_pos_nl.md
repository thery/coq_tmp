---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: nl
---

# square_pos

Laat `a b : Z`{.var}. Als `0 < a < b`{.hyp}, dan `a * a < b * b`{.claim}.

- Het volstaat te bewijzen dat `0 < b * b - a * a`{.claim}.
  - Dit komt neer op `0 < (b + a) * (b - a)`{.claim}.
    - Omdat `0 < a < b`{.fact}, hebben we `0 < b + a /\ 0 < b - a`{.claim}.
