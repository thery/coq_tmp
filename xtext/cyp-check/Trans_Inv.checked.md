<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.thesis. -->

# Trans_Inv

✅ Let `E : Set`. Let `R : Rel E`. Assume `Trans E R` (h). Let `x y z : E`. Assume `Inv E R x y` (h1) and `Inv E R y z` (h2). We prove `Inv E R x z`.

- ✅ By h2 we have `Inv E R y z`, that is `R z y`.
- ✅ By h1 we have `Inv E R x y`, that is `R y x`.
- ✅ By h we have `Trans E R`, that is `forall x0 y0 z0 : E, R x0 y0 -> R y0 z0 -> R x0 z0`.
- ✅ We deduce `R z x`, that is `Inv E R x z`.

