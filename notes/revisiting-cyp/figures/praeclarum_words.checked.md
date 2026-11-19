---
require: From Stdlib Require Import Arith.
---

# praeclarum

✅ Let `x y z t : Prop`. If `x -> z` and `y -> t` then `(x /\ y) -> (z /\ t)`.

- ▫️ Suppose `x /\ y`.
  - ✅ We have `x` and hence `z`.
  - ✅ We have `y` and hence `t`.
  - ✅ Altogether we have `z /\ t`.
