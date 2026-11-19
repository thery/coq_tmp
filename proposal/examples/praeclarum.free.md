---
require: From Stdlib Require Import Arith.
---

# praeclarum

Let `x y z t : Prop`{.var}. If `x -> z`{.hyp} and `y -> t`{.hyp} then `(x /\ y) -> (z /\ t)`{.claim}.

[Suppose `x /\ y`{.hyp}. [[We have `x`{.claim}]{.p}, so by `x -> z`{.fact} we get `z`{.claim}.]{.p} [[We have `y`{.claim}]{.p}, so by `y -> t`{.fact} we get `t`{.claim}.]{.p} Altogether we have `z /\ t`{.claim}.]{.p}
