---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_succ_r

Let `n m : nat`{.var}. We prove `n + S m = S (n + m)`{.claim}.

- By *arith*{.just} we have `n + S m = S (n + m)`{.claim}.
