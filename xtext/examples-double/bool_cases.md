---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.inductive.
by: tauto | congruence | lia | firstorder | auto
---

# bool_cases

Let `b : bool`{.var}. We prove `b = true \/ b = false`{.claim}.

- We prove `b = true \/ b = false`{.fact} by case analysis on `b`{.fact} (bool, match):
- Case 1: we prove `true = true \/ true = false`{.claim}.
  - By definition of eq (eq_refl), we have `true = true`{.claim} *by eapply @eq_refl; eauto*.
  - By definition of or (or_introl), we have `true = true \/ true = false`{.claim} *by eapply @or_introl; eauto*.
- Case 2: we prove `false = true \/ false = false`{.claim}.
  - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
  - By definition of or (or_intror), we have `false = true \/ false = false`{.claim} *by eapply @or_intror; eauto*.
- These cases being exhaustive, we deduce `b = true \/ b = false`{.claim} *by destruct b; cbn; eauto*.
