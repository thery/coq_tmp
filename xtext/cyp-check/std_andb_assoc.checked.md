---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations.
flags: -R /home/thery/git/coq_tmp-xtextnt/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# andb_assoc

✅ Let `b1 b2 b3 : bool`{.var}. We prove `b1 && (b2 && b3) = b1 && b2 && b3`{.claim}.

- ✅ By *tauto*{.just} we have `b1 && (b2 && b3) = b1 && b2 && b3`{.claim}.
