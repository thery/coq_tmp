---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
---

# sqrt_sq_md

Let `a b : Z`{.var}. If `0 <= a`{.hyp} and `0 <= b`{.hyp} then `0 <= Z.sqrt a * Z.sqrt a + Z.sqrt b`{.claim}.

- We have `0 <= Z.sqrt a`{.claim}.
- We have `0 <= Z.sqrt b`{.claim}.
- So `0 <= Z.sqrt a * Z.sqrt a`{.claim}.
  - It suffices to prove `0 <= Z.sqrt a`{.claim}.
