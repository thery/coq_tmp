---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# sqrt_le

Let `a b : nat`{.var}. Assume `a <= b`{.hyp} (h). We prove `Nat.sqrt a <= b /\ (0 < a -> 0 < b)`{.claim}.

- We have `Nat.sqrt a <= a`{.claim}.
- Assume `0 < a`{.hyp} (ha). Then `0 < b`{.claim}.
- Hence `Nat.sqrt a <= b /\ (0 < a -> 0 < b)`{.claim}.
