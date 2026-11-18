---
require: From Stdlib Require Import ZArith Lia.
scope: Z
by: lia | nia
lang: zh
---

# square_pos

设`a b : Z`。若`0 < a < b`，则`a * a < b * b`。

- 只需证明`0 < b * b - a * a`。
- 即证`0 < (b + a) * (b - a)`。
- 因为`0 < a < b`，所以`0 < b + a`且`0 < b - a`。
