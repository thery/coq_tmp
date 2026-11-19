---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_comm

Let `n m : nat`{.var}. We prove `n + m = m + n`{.claim}.

- By *lia*{.just} we have `n + m = m + n`{.claim}.
