<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# orb_comm

✅ Let `b1 b2 : bool`. We prove `b1 || b2 = b2 || b1`.

- ▫️ We prove `b1 || b2 = b2 || b1` by case analysis on `b2` (bool, match):
- ✅ Case 1: we prove `b1 || true = true || b1`.
  - ▫️ We prove `b1 || true = true || b1` by case analysis on `b1` (bool, match):
  - ✅ Case 1.1: we prove `true || true = true || true`.
    - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
  - ✅ Case 1.2: we prove `false || true = true || false`.
    - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
  - ✅ These cases being exhaustive, we deduce `b1 || true = true || b1` .*by destruct b1; cbn; eauto*
- ✅ Case 2: we prove `b1 || false = false || b1`.
  - ▫️ We prove `b1 || false = false || b1` by case analysis on `b1` (bool, match):
  - ✅ Case 2.1: we prove `true || false = false || true`.
    - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
  - ✅ Case 2.2: we prove `false || false = false || false`.
    - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
  - ✅ These cases being exhaustive, we deduce `b1 || false = false || b1` .*by destruct b1; cbn; eauto*
- ✅ These cases being exhaustive, we deduce `b1 || b2 = b2 || b1` .*by destruct b2; cbn; eauto*

