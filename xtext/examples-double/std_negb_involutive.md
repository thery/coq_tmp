---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# negb_involutive

Let `b : bool`{.var}. We prove `negb (negb b) = b`{.claim}.

- We prove `negb (negb b) = b`{.fact} by case analysis on `b`{.fact} (bool, match):
- Case 1: we prove `negb (negb true) = true`{.claim}.
  - By definition of eq (eq_refl), we have `true = true`{.claim} *by eapply @eq_refl; eauto*.
- Case 2: we prove `negb (negb false) = false`{.claim}.
  - By definition of eq (eq_refl), we have `false = false`{.claim} *by eapply @eq_refl; eauto*.
- These cases being exhaustive, we deduce `negb (negb b) = b`{.claim} *by destruct b; cbn; eauto*.
