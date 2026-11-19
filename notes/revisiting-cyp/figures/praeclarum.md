---
require: From Stdlib Require Import Arith.
---

# praeclarum

Let `x y z t : Prop`{.var}. If `x -> z`{.hyp} and `y -> t`{.hyp} then `(x /\ y) -> (z /\ t)`{.claim}.

- Suppose `x /\ y`{.hyp}.
  - We have `x`{.claim} and hence `z`{.claim}.
  - We have `y`{.claim} and hence `t`{.claim}.
  - Altogether we have `z /\ t`{.claim}.
