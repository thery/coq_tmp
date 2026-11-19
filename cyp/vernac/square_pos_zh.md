---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: zh
---

# square_pos

设`a b : Z`{.var}。若`0 < a < b`{.hyp}，则`a * a < b * b`{.claim}。

- 只需证明`0 < b * b - a * a`{.claim}。
  - 即证`0 < (b + a) * (b - a)`{.claim}。
    - 因为`0 < a < b`{.fact}，所以`0 < b + a /\ 0 < b - a`{.claim}。
