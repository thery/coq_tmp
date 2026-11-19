---
require: From Stdlib Require Import Arith Lia.
by: lia
---

# claims_demo

Let `a b : nat`. Assume `a <= b` (hab). We prove `a <= b + 2 /\ a <= b + 3`.

- We have `a <= b + 1` and `a <= b + 2` and `0 <= a`.
- We have `a <= b + 3` and `a <= S b`.
  - We have `a <= b + 4`.
  - We have `a <= b + 5`.
- Let `x y : nat`.
  - Assume `x <= y` (hxy).
    - We have `x <= y + 1` and `x <= y + 2`.
    - We have `x <= y + 3` and `x + 0 <= y + 3`.
      - We have `x <= y + 4`.
    - Let `z : nat`.
      - Assume `y <= z`.
        - We have `x <= z` and `x <= z + 1`.
    - We have `x <= y + 6`.
- Let `u : nat`.
  - We have `u <= u + 1`.
- Hence `a <= b + 2 /\ a <= b + 3`.
