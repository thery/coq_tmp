<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# f_equal

✅ Let `A B : Type`. Let `f : A -> B`. Let `x y : A`. Assume `x = y` (H). We prove `f x = f y`.

- ✅ Going back to the definition of eq (match) in `x = y` (H), we prove `f x = f y`:
  - ✅ By definition of eq (eq_refl), we have `f x = f x` .*by eapply @eq_refl; eauto*

