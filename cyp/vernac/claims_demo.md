---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# claims_demo

Let `a b : nat`{.var}. Assume `a <= b`{.hyp} (hab). We prove `a <= b + 2 /\ a <= b + 3`{.claim}.

- We have `a <= b + 1`{.claim}.
- We have `a <= b + 2`{.claim}, from the node before it.
- We have `a <= b + 3 /\ a <= S b`{.claim}, since
  - we have `a <= b + 4`{.claim} (h4),
  - and `a <= b + 5`{.claim}.
- Let `x y : nat`{.var}; assume `x <= y`{.hyp} (hxy).
  - We have `x <= y + 1 /\ x <= y + 2`{.claim}.
  - We have `x <= y + 3`{.claim} (h3), since
    - `x <= y + 4`{.claim}.
  - Let `z : nat`{.var}; assume `y <= z`{.hyp}. Then `x <= z /\ x <= z + 1`{.claim}.

  So by *h3*{.just} and *lia*{.just} we have `x <= y + 6`{.claim}.
- Let `u : nat`{.var}. We have `u <= u + 1`{.claim}.
- Hence `a <= b + 2 /\ a <= b + 3`{.claim}.
