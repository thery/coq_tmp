<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# andb_assoc

✅ Let `b1 b2 b3 : bool`. We prove `b1 && (b2 && b3) = b1 && b2 && b3`.

- ▫️ We prove `b1 && (b2 && b3) = b1 && b2 && b3` by case analysis on `b3` (bool, match):
- ✅ Case 1: we prove `b1 && (b2 && true) = b1 && b2 && true`.
  - ▫️ We prove `b1 && (b2 && true) = b1 && b2 && true` by case analysis on `b2` (bool, match):
  - ✅ Case 1.1: we prove `b1 && (true && true) = b1 && true && true`.
    - ▫️ We prove `b1 && (true && true) = b1 && true && true` by case analysis on `b1` (bool, match):
    - ✅ Case 1.1.1: we prove `true && (true && true) = true && true && true`.
      - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
    - ✅ Case 1.1.2: we prove `false && (true && true) = false && true && true`.
      - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
    - ✅ These cases being exhaustive, we deduce `b1 && (true && true) = b1 && true && true` .*by destruct b1; cbn; eauto*
  - ✅ Case 1.2: we prove `b1 && (false && true) = b1 && false && true`.
    - ▫️ We prove `b1 && (false && true) = b1 && false && true` by case analysis on `b1` (bool, match):
    - ✅ Case 1.2.1: we prove `true && (false && true) = true && false && true`.
      - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
    - ✅ Case 1.2.2: we prove `false && (false && true) = false && false && true`.
      - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
    - ✅ These cases being exhaustive, we deduce `b1 && (false && true) = b1 && false && true` .*by destruct b1; cbn; eauto*
  - ✅ These cases being exhaustive, we deduce `b1 && (b2 && true) = b1 && b2 && true` .*by destruct b2; cbn; eauto*
- ✅ Case 2: we prove `b1 && (b2 && false) = b1 && b2 && false`.
  - ▫️ We prove `b1 && (b2 && false) = b1 && b2 && false` by case analysis on `b2` (bool, match):
  - ✅ Case 2.1: we prove `b1 && (true && false) = b1 && true && false`.
    - ▫️ We prove `b1 && (true && false) = b1 && true && false` by case analysis on `b1` (bool, match):
    - ✅ Case 2.1.1: we prove `true && (true && false) = true && true && false`.
      - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
    - ✅ Case 2.1.2: we prove `false && (true && false) = false && true && false`.
      - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
    - ✅ These cases being exhaustive, we deduce `b1 && (true && false) = b1 && true && false` .*by destruct b1; cbn; eauto*
  - ✅ Case 2.2: we prove `b1 && (false && false) = b1 && false && false`.
    - ▫️ We prove `b1 && (false && false) = b1 && false && false` by case analysis on `b1` (bool, match):
    - ✅ Case 2.2.1: we prove `true && (false && false) = true && false && false`.
      - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
    - ✅ Case 2.2.2: we prove `false && (false && false) = false && false && false`.
      - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
    - ✅ These cases being exhaustive, we deduce `b1 && (false && false) = b1 && false && false` .*by destruct b1; cbn; eauto*
  - ✅ These cases being exhaustive, we deduce `b1 && (b2 && false) = b1 && b2 && false` .*by destruct b2; cbn; eauto*
- ✅ These cases being exhaustive, we deduce `b1 && (b2 && b3) = b1 && b2 && b3` .*by destruct b3; cbn; eauto*

