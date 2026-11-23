---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# errors

Let `n : nat`{.var}. Assume `n <= 3`{.hyp} (h). We prove `n <= 5`{.claim}.

- We have `n <= 2`{.claim}.
- By *no_such_lemma*{.just} we have `n <= 6`{.claim}.
- From `n <= 1`{.fact} we have `n <= 7`{.claim}.
- Assume `n = 0`{.hyp} (k).
  - By *k*{.just}, `n <= 1`{.claim}.
- By *k*{.just} we have `n <= 8`{.claim}.
- We prove `n <= 9`{.claim}:
  - We have `n <= 4`{.claim}.

  So `n <= 9`{.claim}.
- We have `n <= 10`{.clam}.
- We have `n <=`{.claim}.
- Hence `n <= 5`{.claim}, by *h*{.just}.
