---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# double_gt

✅ Let `n : nat`{.var}. Assume `0 < n`{.hyp} (h). We prove `n < 2 * n`{.claim}.

- ✅ From `0 < n`{.fact} we get `n + 0 < n + n`{.claim}.
- ✅ This is `n < 2 * n`{.claim}, since `2 * n` is `n + n`.
