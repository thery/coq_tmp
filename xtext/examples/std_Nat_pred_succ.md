---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.pred_succ

Let `n : nat`{.var}. We prove `n = n`{.claim}.

- By definition of eq (eq_refl), we have `n = n`{.claim} *by eapply @eq_refl; eauto*.
