---
require: From Stdlib Require Import Arith Lia List Bool. Import ListNotations. Require Import XText.paper.
flags: -R /home/thery/git/coq_tmp-goals/xtext XText
by: tauto | congruence | lia | firstorder | auto
---

# identity

✅ Let `A : Prop`{.var}. Assume `A`{.hyp} (h). We prove `A`{.claim}.

- ✅ By *h*{.just} we have `A`{.claim}.
