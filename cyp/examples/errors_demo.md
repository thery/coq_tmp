---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# errors_demo

Let `n : nat`{.var}. Assume `n <= 3`{.hyp} (h). We prove `n <= 5`{.claim}.

- A remark: nothing here is tagged, `n` included; it is shown, not checked.
- From `n <= 4`{.fact} we have `n <= 6`{.claim}.
- By *no_such_lemma*{.just} we have `n <= 7`{.claim}.
- Assume `n = 0`{.hyp} (k).
  - We have `n <= 1`{.claim} by *k*{.just} and *lia*{.just}.
- By *k*{.just} we have `n <= 8`{.claim}.
- Hence `n <= 5`{.claim}, by *h*{.just} and *lia*{.just}.
