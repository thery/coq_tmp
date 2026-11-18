---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# andb_assoc

Let `b1 b2 b3 : bool`{.var}. We prove `b1 && (b2 && b3) = b1 && b2 && b3`{.claim}.

- We prove `b1 && (b2 && b3) = b1 && b2 && b3`{.fact} by case analysis on `b3`{.fact} (bool, match):
- Case 1: we prove `b1 && (b2 && true) = b1 && b2 && true`{.claim}.
  - We prove `b1 && (b2 && true) = b1 && b2 && true`{.fact} by case analysis on `b2`{.fact} (bool, match):
  - Case 1.1: we prove `b1 && (true && true) = b1 && true && true`{.claim}.
    - We prove `b1 && (true && true) = b1 && true && true`{.fact} by case analysis on `b1`{.fact} (bool, match):
    - Case 1.1.1: we prove `true && (true && true) = true && true && true`{.claim}.
      - By definition of eq (eq_refl), we have `true = true`{.claim} *by eapply @eq_refl; eauto*.
    - Case 1.1.2: we prove `false && (true && true) = false && true && true`{.claim}.
      - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
    - These cases being exhaustive, we deduce `b1 && (true && true) = b1 && true && true`{.claim} *by destruct b1; cbn; eauto*.
  - Case 1.2: we prove `b1 && (false && true) = b1 && false && true`{.claim}.
    - We prove `b1 && (false && true) = b1 && false && true`{.fact} by case analysis on `b1`{.fact} (bool, match):
    - Case 1.2.1: we prove `true && (false && true) = true && false && true`{.claim}.
      - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
    - Case 1.2.2: we prove `false && (false && true) = false && false && true`{.claim}.
      - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
    - These cases being exhaustive, we deduce `b1 && (false && true) = b1 && false && true`{.claim} *by destruct b1; cbn; eauto*.
  - These cases being exhaustive, we deduce `b1 && (b2 && true) = b1 && b2 && true`{.claim} *by destruct b2; cbn; eauto*.
- Case 2: we prove `b1 && (b2 && false) = b1 && b2 && false`{.claim}.
  - We prove `b1 && (b2 && false) = b1 && b2 && false`{.fact} by case analysis on `b2`{.fact} (bool, match):
  - Case 2.1: we prove `b1 && (true && false) = b1 && true && false`{.claim}.
    - We prove `b1 && (true && false) = b1 && true && false`{.fact} by case analysis on `b1`{.fact} (bool, match):
    - Case 2.1.1: we prove `true && (true && false) = true && true && false`{.claim}.
      - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
    - Case 2.1.2: we prove `false && (true && false) = false && true && false`{.claim}.
      - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
    - These cases being exhaustive, we deduce `b1 && (true && false) = b1 && true && false`{.claim} *by destruct b1; cbn; eauto*.
  - Case 2.2: we prove `b1 && (false && false) = b1 && false && false`{.claim}.
    - We prove `b1 && (false && false) = b1 && false && false`{.fact} by case analysis on `b1`{.fact} (bool, match):
    - Case 2.2.1: we prove `true && (false && false) = true && false && false`{.claim}.
      - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
    - Case 2.2.2: we prove `false && (false && false) = false && false && false`{.claim}.
      - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
    - These cases being exhaustive, we deduce `b1 && (false && false) = b1 && false && false`{.claim} *by destruct b1; cbn; eauto*.
  - These cases being exhaustive, we deduce `b1 && (b2 && false) = b1 && b2 && false`{.claim} *by destruct b2; cbn; eauto*.
- These cases being exhaustive, we deduce `b1 && (b2 && b3) = b1 && b2 && b3`{.claim} *by destruct b3; cbn; eauto*.
