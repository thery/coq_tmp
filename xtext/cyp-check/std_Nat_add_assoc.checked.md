---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# Nat.add_assoc

✅ Let `n m p : nat`{.var}. We prove `n + (m + p) = n + m + p`{.claim}.

- ✅ We have `n + (m + p) = n + m + p`{.claim} *by lia*.
