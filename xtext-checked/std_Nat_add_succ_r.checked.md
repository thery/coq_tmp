---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_succ_r

✅ Let `n m : nat`{.var}. We prove `n + S m = S (n + m)`{.claim}.

- ✅ We have `n + S m = S (n + m)`{.claim} *by lia*.
