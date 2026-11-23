---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-xtextnt/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_0_r

✅ Let `n : nat`{.var}. We prove `n + 0 = n`{.claim}.

- ✅ By *tauto*{.just} we have `n + 0 = n`{.claim}.
