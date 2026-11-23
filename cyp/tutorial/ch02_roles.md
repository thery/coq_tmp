---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# roles

Let `a b : nat`{.var} and `s := a + b`{.var}. Assume `a <= b`{.hyp} (hab) and `b <= 10`{.hyp}. We prove `s <= 20`{.claim}.

- This line is a remark: it has no tag, so cyp shows it and checks nothing.
- By *hab*{.just} and *H1*{.just} we have `a <= 10`{.claim} (ha).
- From `a <= 10`{.fact} and `b <= 10`{.fact} we get `a + b <= 20`{.claim}.
- As `s` is `a + b`, we have `s <= 20`{.claim}.
