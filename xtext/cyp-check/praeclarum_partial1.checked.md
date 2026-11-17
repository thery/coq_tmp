<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.partial. -->

# praeclarum_partial1 (proof in progress)

✅ Let `x y z t : Prop`. Assume `(x -> z) /\ (y -> t)` (H). We prove `x /\ y -> z /\ t`.

- ✅ Going back to the definition of and (match) in `(x -> z) /\ (y -> t)` (H), we prove `x /\ y -> z /\ t`:
  - ▫️ Assume `x -> z` (Hxz) and `y -> t` (Hyt) and `x /\ y` (H0).
    - ✅ Going back to the definition of and (match) in `x /\ y` (H0), we prove `z /\ t`:
      - ▫️ Assume `x` (Hx) and `y` (Hy).
        - ✅ Prove `z`.
        - ✅ Prove `t`.
        - ✅ So by definition of and (conj), we have `z /\ t` .*by eapply @conj; eauto*

