---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# facts

✅ Let `n : nat`{.var}. Assume `n <= 3`{.hyp} (h). We prove `n <= 5`{.claim}.

- ✅ From the hypothesis `n <= 3`{.fact} we get `n <= 4`{.claim}.
- ✅ From the step before, `n <= 4`{.fact}, we get `n <= 6`{.claim}.
- ❌ We claim `n <= 2`{.claim}, which does not hold.

  <details><summary>not proved: n <= 2</summary></details>

- ✅ From `n <= 2`{.fact} we get `n <= 7`{.claim}.
- ❌ From `n <= 1`{.fact} we get `n <= 8`{.claim}.

  <details><summary>the fact n <= 1 is no hypothesis or conclusion visible here</summary></details>

- ✅ Hence `n <= 5`{.claim}.
