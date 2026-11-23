---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_0_r

Let `n : nat`{.var}. We prove `n + 0 = n`{.claim}.

- By *arith*{.just} we have `n + 0 = n`{.claim}.
