---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-xtextnt/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Nat.mul_comm

Let `n m : nat`{.var}. We prove `n * m = m * n`{.claim}.

- By *arith*{.just} we have `n * m = m * n`{.claim}.
