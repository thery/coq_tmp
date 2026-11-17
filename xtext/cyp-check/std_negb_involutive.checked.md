<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# negb_involutive

✅ Let `b : bool`. We prove `negb (negb b) = b`.

- ▫️ We prove `negb (negb b) = b` by case analysis on `b` (bool, match):
- ✅ Case 1: we prove `negb (negb true) = true`.
  - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
- ✅ Case 2: we prove `negb (negb false) = false`.
  - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
- ✅ These cases being exhaustive, we deduce `negb (negb b) = b` .*by destruct b; cbn; eauto*

