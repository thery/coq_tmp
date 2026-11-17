<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper. -->

# praeclarum

✅ Let `x y z t : Prop`. Assume `(x -> z) /\ (y -> t)` (h1) and `x /\ y` (h2). We prove `z /\ t`.

- ✅ Going back to the definition of and (and_ind) in `(x -> z) /\ (y -> t)` (h1), we prove `z /\ t`:
  - ▫️ Assume `x -> z` (i) and `y -> t` (j).
    - ✅ Going back to the definition of and (and_ind) in `x /\ y` (h2), we prove `z /\ t`:
      - ▫️ Assume `x` (k) and `y` (l).
        - ✅ We deduce `z`.
          - ✅ By k we have `x`.
          - ✅ By i we have `x -> z`.
        - ✅ We deduce `t`.
          - ✅ By l we have `y`.
          - ✅ By j we have `y -> t`.
        - ✅ So by definition of and (conj), we have `z /\ t` .*by eapply @conj; eauto*

