---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# even_plus_two

✅ Let `n : nat`{.var}. Assume `exists k, n = 2 * k`{.hyp} (h). We prove `exists k, n + 2 = 2 * k`{.claim}.

- ✅ By case analysis (*match*{.just}) on *h*{.just}, of type *ex*{.just}, we prove `exists k, n + 2 = 2 * k`{.claim}:
  - ✅ Let `k : nat`{.var} and assume `n = 2 * k`{.hyp} (hk).
    - ✅ Then `n + 2 = 2 * (k + 1)`{.claim} (e), by *hk*{.just}.

    So `exists k, n + 2 = 2 * k`{.claim}, with `k + 1` as the witness (*ex_intro*{.just}, *e*{.just}).
