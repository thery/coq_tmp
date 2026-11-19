---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.pred_succ

Let `n : nat`{.var}. We prove `Nat.pred (S n) = n`{.claim}.

- By definition of eq (*eq_refl*{.just}), we have `n = n`, that is `Nat.pred (S n) = n`{.claim}.
