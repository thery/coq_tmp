<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# eq_sym

✅ Let `A : Type`. Let `x y : A`. Assume `x = y` (H). We prove `y = x`.

- ✅ Going back to the definition of eq (match) in `x = y` (H), we prove `y = x`:
  - ✅ By definition of eq (eq_refl), we have `x = x` .*by eapply @eq_refl; eauto*

