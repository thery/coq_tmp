<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# eq_trans

✅ Let `A : Type`. Let `x y z : A`. Assume `x = y` (H) and `y = z` (H0). We prove `x = z`.

- ✅ Going back to the definition of eq (match) in `y = z` (H0), we prove `x = z`:
  - ✅ By H we have `x = y`.

