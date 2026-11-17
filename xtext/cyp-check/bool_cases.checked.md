<!-- checked by cyp; prelude: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive. -->

# bool_cases

✅ Let `b : bool`. We prove `b = true \/ b = false`.

- ▫️ We prove `b = true \/ b = false` by case analysis on `b` (bool, match):
- ✅ Case 1: we prove `true = true \/ true = false`.
  - ✅ By definition of eq (eq_refl), we have `true = true` .*by eapply @eq_refl; eauto*
  - ✅ By definition of or (or_introl), we have `true = true \/ true = false` .*by eapply @or_introl; eauto*
- ✅ Case 2: we prove `false = true \/ false = false`.
  - ✅ By definition of eq (eq_refl), we have `false = false` .*by eapply @eq_refl; eauto*
  - ✅ By definition of or (or_intror), we have `false = true \/ false = false` .*by eapply @or_intror; eauto*
- ✅ These cases being exhaustive, we deduce `b = true \/ b = false` .*by destruct b; cbn; eauto*

