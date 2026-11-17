<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper. -->

# nearly_reflexive

✅ Let `A : Set`. Let `R : A -> A -> Prop`. Assume `forall x y : A, R x y -> R y x` (symmetry) and `forall x y z : A, R x y -> R y z -> R x z` (transitivity). Let `x : A`. Assume `exists y0 : A, R x y0` (h). We prove `R x x`.

- ✅ Going back to the definition of ex (ex_ind) in `exists y0 : A, R x y0` (h), we prove `R x x`:
  - ▫️ Let us consider an arbitrary `y0 : A`.
    - ▫️ Assume `R x y0` (i).
      - ✅ By i we have `R x y0`.
      - ✅ We deduce `R y0 x`.
        - ✅ By i we have `R x y0`.
        - ✅ By symmetry we have `forall x0 y : A, R x0 y -> R y x0`.
      - ✅ By transitivity we have `forall x0 y z : A, R x0 y -> R y z -> R x0 z`.
      - ✅ We deduce `R x x`.

