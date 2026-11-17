<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# orb_false_r

✅ Let `b : bool`. We prove `b || false = b`.

- ▫️ We prove `b || false = b` by case analysis on `b` (bool, match):
- ✅ Case 1: we prove `true || false = true`.
  - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
- ✅ Case 2: we prove `false || false = false`.
  - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
- ✅ These cases being exhaustive, we deduce `b || false = b` .*by destruct b; cbn; eauto*

