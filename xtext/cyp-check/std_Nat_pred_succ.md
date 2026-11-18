---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-xtext/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Nat.pred_succ

Let `n : nat`{.var}. We prove `Nat.pred (S n) = n`{.claim}.

- By definition of eq (eq_refl), we have `n = n`{.claim} *by Corelib.Init.Logic.eq_refl*, that is `Nat.pred (S n) = n`{.fact}.
