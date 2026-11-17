<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. -->

# andb_true_r

✅ Let `b : bool`. We prove `b && true = b`.

- ▫️ We prove `b && true = b` by case analysis on `b` (bool, match):
- ✅ Case 1: we prove `true && true = true`.
  - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
- ✅ Case 2: we prove `false && true = false`.
  - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
- ✅ These cases being exhaustive, we deduce `b && true = b` .*by destruct b; cbn; eauto*

