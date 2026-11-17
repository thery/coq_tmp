<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# Trans_Inv

✅ Let `E : Set`. Let `R : Rel E`. Assume `Trans E R` (h). Let `x y z : E`. Assume `Inv E R x y` (h1) and `Inv E R y z` (h2). We prove `R z x`.

- ✅ By h2 we have `Inv E R y z`.
- ✅ By h1 we have `Inv E R x y`.
- ✅ In particular `R z y -> R y x -> R z x`.
  - ✅ By h we have `Trans E R`.
- ✅ We deduce `R z x`.

