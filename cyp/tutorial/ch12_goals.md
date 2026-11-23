---
require: From Stdlib Require Import ZArith Lia.
scope: Z_scope
by: lia
---

# goals

Let `a b : Z`{.var}. Assume `0 <= a`{.hyp} and `0 <= b`{.hyp}. We prove `0 <= Z.sqrt a + Z.sqrt b + a`{.claim}.

- We have `0 <= Z.sqrt a`{.claim}.
- Prove `0 <= Z.sqrt b`{.goal}.
- Hence `0 <= Z.sqrt a + Z.sqrt b + a`{.claim}.
