<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# negb_andb

✅ Let `b1 b2 : bool`. We prove `negb (b1 && b2) = negb b1 || negb b2`.

- ▫️ We prove `negb (b1 && b2) = negb b1 || negb b2` by case analysis on `b2` (bool, match):
- ✅ Case 1: we prove `negb (b1 && true) = negb b1 || negb true`.
  - ▫️ We prove `negb (b1 && true) = negb b1 || negb true` by case analysis on `b1` (bool, match):
  - ✅ Case 1.1: we prove `negb (true && true) = negb true || negb true`.
    - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
  - ✅ Case 1.2: we prove `negb (false && true) = negb false || negb true`.
    - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
  - ✅ These cases being exhaustive, we deduce `negb (b1 && true) = negb b1 || negb true` .*by destruct b1; cbn; eauto*
- ✅ Case 2: we prove `negb (b1 && false) = negb b1 || negb false`.
  - ▫️ We prove `negb (b1 && false) = negb b1 || negb false` by case analysis on `b1` (bool, match):
  - ✅ Case 2.1: we prove `negb (true && false) = negb true || negb false`.
    - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
  - ✅ Case 2.2: we prove `negb (false && false) = negb false || negb false`.
    - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
  - ✅ These cases being exhaustive, we deduce `negb (b1 && false) = negb b1 || negb false` .*by destruct b1; cbn; eauto*
- ✅ These cases being exhaustive, we deduce `negb (b1 && b2) = negb b1 || negb b2` .*by destruct b2; cbn; eauto*

